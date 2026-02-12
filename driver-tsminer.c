#include <float.h>
#include <limits.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <strings.h>
#include <sys/time.h>
#include <unistd.h>
#include <math.h>

#include "config.h"

#include "compat.h"
#include "miner.h"
#include "usbutils.h"

// The serial I/O speed - Linux uses a define 'B115200' in bits/termios.h
#define TSMINER_IO_SPEED 2000000

#define TSMINER_BUF_SIZE 4
// The size of a successful nonce read
#define TSMINER_READ_SIZE 4

// Ensure the sizes are correct for the Serial read

#define ASSERT1(condition) __maybe_unused static char sizeof_uint32_t_must_be_4[(condition)?1:-1]
ASSERT1(sizeof(uint32_t) == 4);

// TODO: USB? Different calculation? - see usbstats to work it out e.g. 1/2 of normal send time
//  or even use that number? 1/2
// #define ICARUS_READ_TIME(baud) ((double)ICARUS_READ_SIZE * (double)8.0 / (double)(baud))
// maybe 1ms?


#define TSMINER_READ_COUNT_TIMING	1500000//necesario miner especial
#define TSMINER_READ_COUNT_TIMINGMAX 1600000//necesario miner especial

#define SECTOMS(s)	((int)((s) * 1000))

#define TSMINER_HASH_TIME 0.0000002//necesario miner especial

#define HISTORY_SEC 60
// Minimum how many points a single ICARUS_HISTORY should have
#define MIN_DATA_COUNT 5
// The value MIN_DATA_COUNT used is doubled each history until it exceeds:
#define MAX_MIN_DATA_COUNT 100

static struct timeval history_sec = { HISTORY_SEC, 0 };

enum timing_mode { MODE_DEFAULT, MODE_SHORT, MODE_LONG, MODE_VALUE };

struct TSMINER_INFO {
	enum sub_ident ident;
	int intinfo;
	int read_time;
	int fail_time;
	enum timing_mode timing_mode;
	uint64_t golden_hashes;
	struct timeval golden_tv;

	int baud;
	int work_division;
	int fpga_count;
	uint32_t nonce_mask;
	int nonce_size;
	double Hs;
	int read_time_limit;
	bool failing;
	pthread_mutex_t lock;
};

#define TSMINER_MIDSTATE_SIZE 32
#define TSMINER_TARGET_SIZE 32
#define TSMINER_WORK_SIZE 12
#define TSMINER_WORK_DATA_OFFSET 64

struct TSMINER_WORK {//work modificado
	uint8_t midstate[TSMINER_MIDSTATE_SIZE];
	uint8_t work[TSMINER_WORK_SIZE];
	uint8_t target[TSMINER_TARGET_SIZE];
};

static int option_offset = -1;

static void _transfer(struct cgpu_info *tsminer, uint8_t request_type, uint8_t bRequest, uint16_t wValue, uint16_t wIndex, uint32_t *data, int siz, enum usb_cmds cmd)
{
	int err;

	err = usb_transfer_data(tsminer, request_type, bRequest, wValue, wIndex, data, siz, cmd);

	applog(LOG_DEBUG, "%s: cgid %d %s got err %d",
			tsminer->drv->name, tsminer->cgminer_id,
			usb_cmdname(cmd), err);
}

#define transfer(tsminer, request_type, bRequest, wValue, wIndex, cmd) \
		_transfer(tsminer, request_type, bRequest, wValue, wIndex, NULL, 0, cmd)

static void tsminer_initialise(struct cgpu_info *tsminer, int baud)
{
	struct TSMINER_INFO *info = (struct TSMINER_INFO *)(tsminer->device_data);
	uint16_t wValue, wIndex;
	enum sub_ident ident;
	int interface;

	info->read_time=TSMINER_READ_COUNT_TIMING;
	info->fail_time=TSMINER_READ_COUNT_TIMING*3;
	info->Hs=TSMINER_HASH_TIME;
	info->read_time_limit=TSMINER_READ_COUNT_TIMINGMAX;

	if (tsminer->usbinfo.nodev)
		return;

	interface = _usb_interface(tsminer, info->intinfo);
	ident = usb_ident(tsminer);
	if(ident==IDENT_TSM){
		transfer(tsminer, FTDI_TYPE_OUT, FTDI_REQUEST_RESET, FTDI_VALUE_RESET,interface, C_RESET);
		if (tsminer->usbinfo.nodev)
			return;
		_usb_ftdi_set_latency(tsminer, info->intinfo);
		if (tsminer->usbinfo.nodev)
			return;
		transfer(tsminer, FTDI_TYPE_OUT, FTDI_REQUEST_DATA, FTDI_VALUE_DATA_BLT,interface, C_SETDATA);
		if (tsminer->usbinfo.nodev)
			return;
		wValue = FTDI_VALUE_BAUD_TSM_2000000;
		wIndex = FTDI_INDEX_BAUD_TSM_2000000;
		transfer(tsminer, FTDI_TYPE_OUT, FTDI_REQUEST_BAUD, wValue,(wIndex & 0xff00) | interface, C_SETBAUD);
		if (tsminer->usbinfo.nodev)
			return;
		transfer(tsminer, FTDI_TYPE_OUT, FTDI_REQUEST_RESET, FTDI_VALUE_PURGE_TX,interface, C_PURGETX);
		if (tsminer->usbinfo.nodev)
			return;
		transfer(tsminer, FTDI_TYPE_OUT, FTDI_REQUEST_RESET, FTDI_VALUE_PURGE_RX,interface, C_PURGERX);
	}
	else
		quit(1, "tsminer_intialise() called with invalid %s cgid %i ident=%d",tsminer->drv->name, tsminer->cgminer_id, ident);
}

static void rev(unsigned char *s, size_t l)
{
	size_t i, j;
	unsigned char t;

	for (i = 0, j = l - 1; i < j; i++, j--) {
		t = s[i];
		s[i] = s[j];
		s[j] = t;
	}
}

#define TSM_NONCE_ERROR -1
#define TSM_NONCE_OK 0
#define TSM_NONCE_RESTART 1
#define TSM_NONCE_TIMEOUT 2

static int tsminer_get_nonce(struct cgpu_info *tsminer, unsigned char *buf, struct timeval *tv_start,
			    struct timeval *tv_finish, struct thr_info *thr, int read_time)
{
	struct TSMINER_INFO *info = (struct TSMINER_INFO *)(tsminer->device_data);
	int err, amt, rc;

	if (tsminer->usbinfo.nodev)
		return TSM_NONCE_ERROR;

	cgtime(tv_start);
	err = usb_read_ii_timeout_cancellable(tsminer, info->intinfo, (char *)buf,
					      info->nonce_size, &amt, read_time,
					      C_GETRESULTS);
	cgtime(tv_finish);

	if (err < 0 && err != LIBUSB_ERROR_TIMEOUT) {
		applog(LOG_ERR, "%s %i: Comms error (rerr=%d amt=%d)", tsminer->drv->name,
		       tsminer->device_id, err, amt);
		dev_error(tsminer, REASON_DEV_COMMS_ERROR);
		return TSM_NONCE_ERROR;
	}

	if (amt >= info->nonce_size)
		return TSM_NONCE_OK;

	rc = SECTOMS(tdiff(tv_finish, tv_start));
	if (thr && thr->work_restart) {
		applog(LOG_DEBUG, "Tsminer Read: Work restart at %d ms", rc);
		return TSM_NONCE_RESTART;
	}

	if (amt > 0)
		applog(LOG_DEBUG, "Tsminer Read: Timeout reading for %d ms", rc);
	else
		applog(LOG_DEBUG, "Tsminer Read: No data for %d ms", rc);
	return TSM_NONCE_TIMEOUT;
}

static void get_options(int this_option_offset, struct cgpu_info *tsminer, int *baud){
	enum sub_ident ident=usb_ident(tsminer);

	if(ident==IDENT_TSM){
		*baud = TSMINER_IO_SPEED;
	}
	else
		quit(1, "Tsminer get_options() called with invalid %s ident=%d",tsminer->drv->name, ident);
}

static void tsminer_clear(struct cgpu_info *tsminer, struct TSMINER_INFO *info)
{
	char buf[512];
	int amt;

	do {
		usb_read_ii_timeout(tsminer, info->intinfo, buf, 512, &amt, 100, C_GETRESULTS);
	} while (amt > 0);
}

static struct cgpu_info *tsminer_detect_one(struct libusb_device *dev, struct usb_find_devices *found)
{
	int this_option_offset = ++option_offset;
	struct TSMINER_INFO *info;
	struct timeval tv_start, tv_finish;

	// Block genesis nonce = (0x7c2bac1d) = 0x1DAC2B7C
	//	aprox 3 min
	const char golden_ob[] =
		"000000000000ffff000000000000000000000000000000000000000000000000"
		"4a5e1e4b495fab291d00ffff"
		"339a90bcf0bf58637daccc90a8ca591ee9d8c8c3c803014f3687b1961bf91947";

	const char golden_nonce[] = "1dac2b7c";
	const uint32_t golden_nonce_val = 0x1DAC2B7C;
	unsigned char nonce_bin[TSMINER_BUF_SIZE];
	struct TSMINER_WORK workdata;
	char *nonce_hex;
	int baud;
	struct cgpu_info *tsminer;
	int ret, err, amount, tries;
	bool ok;

	if ((sizeof(workdata) << 1) != (sizeof(golden_ob)-1))
		quithere(1, "Data and golden_ob sizes don't match");

	tsminer = usb_alloc_cgpu(&tsminer_drv, 1);

	if (!usb_init(tsminer, dev, found))
		goto shin;
//modificacion especial
	/*struct libusb_device_descriptor desc;  
	libusb_get_device_descriptor(dev, &desc);  
	if (desc.idVendor == 0x0403 && desc.idProduct == 0x6001) {  
		// Forzar el driver TSM  
		cgpu->drv = &tsminer_drv;  
		cgpu->drv->name = "TSM";  
		// Continuar con la detección normal...  
	}*/
//fin modificacion especial
	get_options(this_option_offset, tsminer, &baud);

	hex2bin((void *)(&workdata), golden_ob, sizeof(workdata));

	info = cgcalloc(1, sizeof(struct TSMINER_INFO));
	tsminer->device_data = (void *)info;
	//mod
	tsminer->usbinfo.nodev = false;  // dispositivo disponible
	//

	info->ident = usb_ident(tsminer);
	if(info->ident!=IDENT_TSM)
		quit(1, "%s tsminer_detect_one() invalid %s ident=%d",tsminer->drv->dname, tsminer->drv->dname, info->ident);
	info->nonce_size = TSMINER_READ_SIZE;

retry:

	tries = 2;
	ok = false;
	while (!ok && tries-- > 0) {
		tsminer_clear(tsminer, info);
		tsminer_initialise(tsminer, baud);

		err = usb_write_ii(tsminer, info->intinfo,(char *)(&workdata), sizeof(workdata), &amount, C_SENDWORK);

		if (err != LIBUSB_SUCCESS || amount != sizeof(workdata))
			continue;

		memset(nonce_bin, 0, sizeof(nonce_bin));
		ret = tsminer_get_nonce(tsminer, nonce_bin, &tv_start, &tv_finish, NULL, TSMINER_READ_COUNT_TIMING);
		if (ret != TSM_NONCE_OK)
			continue;
		//rev(nonce_bin,4);
		nonce_hex = bin2hex(nonce_bin, sizeof(nonce_bin));
		applog(LOG_INFO,
					"tsminer Detect: "
					"data received at %s: get %s, should: %s",
					tsminer->device_path, nonce_hex, golden_nonce);
		if (strncmp(nonce_hex, golden_nonce, 8) == 0) {
			ok = true;
			continue;
		} else {
			if (tries < 0) {
				applog(LOG_INFO,
					"tsminer Detect: "
					"Test failed at %s: get %s, should: %s",
					tsminer->device_path, nonce_hex, golden_nonce);
			}
		}
		free(nonce_hex);
	}

	if (!ok) {
		goto unshin;
	} else {
		if (info->ident == IDENT_TSM) {
			applog(LOG_DEBUG,
				"Tsminer Detect: "
				"Test succeeded at %s i%d: got %s",
					tsminer->device_path, info->intinfo, golden_nonce);
		}
		else
			goto retry;
	}

	if (!add_cgpu(tsminer))
		goto unshin;
	applog(LOG_INFO, "add_cgpu OK, nodev=%s", tsminer->usbinfo.nodev ? "true" : "false");

	update_usb_stats(tsminer);

	applog(LOG_INFO, "%s %d: Found at %s",
		tsminer->drv->name, tsminer->device_id, tsminer->device_path);

	applog(LOG_DEBUG, "%s %d: Init baud=%d work_division= 1 fpga_count= 1 ",
		tsminer->drv->name, tsminer->device_id, baud);

	info->baud = baud;
	info->work_division = 1;
	info->fpga_count = 1;
	info->nonce_mask = 0xffffffff;

	info->golden_hashes = (golden_nonce_val & info->nonce_mask);
	timersub(&tv_finish, &tv_start, &(info->golden_tv));
	applog(LOG_INFO,
					"operacion satisfactoria"
					"golden nonce encontrado, nodev: %s nombre %s",
					tsminer->usbinfo.nodev, tsminer->drv->name);
	return tsminer;

unshin:

	usb_uninit(tsminer);
	free(info);
	tsminer->device_data = NULL;
	//
	tsminer->usbinfo.nodev = true; // el dispositivo ya no está disponible
	//

shin:

	tsminer = usb_free_cgpu(tsminer);

	return NULL;
}

static void tsminer_detect(bool __maybe_unused hotplug)
{
	usb_detect(&tsminer_drv, tsminer_detect_one);
	applog(LOG_INFO,
					"operacion satisfactoria"
					" FPGA localizado");
}

static bool tsminer_prepare(struct thr_info *thr)
{
	return true;
}

static int64_t tsminer_scanwork(struct thr_info *thr){
	struct cgpu_info *tsminer = thr->cgpu;
	struct TSMINER_INFO *info = (struct TSMINER_INFO *)(tsminer->device_data);
	int ret, err, amount;
	unsigned char nonce_bin[TSMINER_BUF_SIZE];
	struct TSMINER_WORK workdata;
	uint32_t nonce;
	char *ob_hex;
	int64_t hash_count = 0;
	struct timeval tv_start, tv_finish, elapsed;
	uint32_t was_hw_error=0;
	struct work *work;
	int64_t estimate_hashes;
	int timeout=info->fail_time;
	applog(LOG_INFO,
					"iniciando scanwork, nodev: %s nombre %s",
					tsminer->usbinfo.nodev, tsminer->drv->name);
	work = get_work(thr, thr->id);
	if (unlikely(!work)) {
		applog(LOG_INFO,
					"fallo del scanwork, nodev: %s nombre %s",
					tsminer->usbinfo.nodev, tsminer->drv->name);
    	return 0;
	}
	applog(LOG_INFO,
					"work obtenido");
	if (tsminer->usbinfo.nodev)
		return -1;
	applog(LOG_INFO,
					"preparando datos de trabajo");
	elapsed.tv_sec = elapsed.tv_usec = 0;
	memset((void *)(&workdata), 0, sizeof(workdata));
	memcpy(&(workdata.midstate), work->midstate, TSMINER_MIDSTATE_SIZE);
	memcpy(&(workdata.work), work->data + TSMINER_WORK_DATA_OFFSET, TSMINER_WORK_SIZE);
	memcpy(&(workdata.target), work->target, TSMINER_TARGET_SIZE);
	//rev((void *)(&(workdata.midstate)), TSMINER_MIDSTATE_SIZE);
	//rev((void *)(&(workdata.work)), TSMINER_WORK_SIZE);
	//rev((void *)(&(workdata.target)), TSMINER_TARGET_SIZE);
	usb_buffer_clear(tsminer);
	err = usb_write_ii(tsminer, info->intinfo, (char *)(&workdata), sizeof(workdata), &amount, C_SENDWORK);
	if (err < 0 || amount != sizeof(workdata)) {
		applog(LOG_ERR, "%s %i: Comms error (werr=%d amt=%d)",
				tsminer->drv->name, tsminer->device_id, err, amount);
		dev_error(tsminer, REASON_DEV_COMMS_ERROR);
		tsminer_initialise(tsminer, info->baud);
		goto out;
	}
	if (opt_debug) {
		ob_hex = bin2hex((void *)(&workdata), sizeof(workdata));
		applog(LOG_DEBUG, "%s %d: sent %s",
			tsminer->drv->name, tsminer->device_id, ob_hex);
		free(ob_hex);
	}

more_nonces:
	memset(nonce_bin, 0, sizeof(nonce_bin));
	ret = tsminer_get_nonce(tsminer, nonce_bin, &tv_start, &tv_finish, thr, timeout);
	timeout-=ms_tdiff(&tv_finish,&tv_start);
	if(timeout<1000 || timeout<0)
		timeout=1000;
	timersub(&tv_finish, &tv_start, &elapsed);	
	if (ret == TSM_NONCE_ERROR){
		applog(LOG_ERR, "%s %i: TSMINER error send data",tsminer->drv->name, tsminer->device_id);
		hash_count=0;
		goto out;
	}
	if (ret == TSM_NONCE_TIMEOUT) {
		estimate_hashes = 0xffffffff;
		applog(LOG_DEBUG, "%s %d: no nonce = 0x%08lX hashes (%ld.%06lds)",
				tsminer->drv->name, tsminer->device_id,
				(long unsigned int)estimate_hashes,
				(long)elapsed.tv_sec, (long)elapsed.tv_usec);
		hash_count = (nonce & info->nonce_mask) + 1;
		goto out;
	}
	if(ret==TSM_NONCE_RESTART){
		estimate_hashes = ((double)(elapsed.tv_sec) + ((double)(elapsed.tv_usec))/((double)1000000)) / info->Hs;
		if (unlikely(estimate_hashes > 0xffffffff))
			estimate_hashes = 0xffffffff;
		applog(LOG_DEBUG, "%s %d: no nonce = 0x%08lX hashes (%ld.%06lds)",
				tsminer->drv->name, tsminer->device_id,
				(long unsigned int)estimate_hashes,
				(long)elapsed.tv_sec, (long)elapsed.tv_usec);
		hash_count = (nonce & info->nonce_mask) + 1;
		goto out;
	}
	if(ret==TSM_NONCE_OK){
		memcpy((char *)&nonce, nonce_bin, TSMINER_READ_SIZE);  
		nonce = htobe32(nonce);
		if (submit_nonce(thr, work, nonce)) {  
			applog(LOG_DEBUG, "%s %i: TSMINER hash encontrado",tsminer->drv->name, tsminer->device_id);
		} else   
			was_hw_error ++;
		hash_count = (nonce & info->nonce_mask) + 1;
		goto more_nonces;
	}
out:
	if(was_hw_error!=0)
		applog(LOG_DEBUG, "%s %i: hashes err: %u",tsminer->drv->name, tsminer->device_id, was_hw_error);
	free_work(work);
	return hash_count;
}

static struct api_data *tsminer_api_stats(struct cgpu_info *cgpu){
	struct api_data *root = NULL;
	struct TSMINER_INFO *info = (struct TSMINER_INFO *)(cgpu->device_data);

	root = api_add_int(root, "read_time", &(info->read_time), false);
	root = api_add_int(root, "read_time_limit", &(info->read_time_limit), false);
	root = api_add_hs(root, "Hs", &(info->Hs), false);
	root = api_add_int(root, "baud", &(info->baud), false);
	root = api_add_int(root, "work_division", &(info->work_division), false);
	root = api_add_int(root, "fpga_count", &(info->fpga_count), false);
	return root;
}

static void tsminer_shutdown(__maybe_unused struct thr_info *thr)
{
	// TODO: ?
}

struct device_drv tsminer_drv = {
	.drv_id = DRIVER_tsminer,
	.dname = "Tsminer",
	.name = "TSM",
	.drv_detect = tsminer_detect,//1 rev
	.hash_work = &hash_driver_work,//1 rev
	.get_api_stats = tsminer_api_stats,//1 rev
	.thread_prepare = tsminer_prepare,//1 rev
	.scanwork = tsminer_scanwork,//1 rev//2 rev
	.thread_shutdown = tsminer_shutdown,//1 rev
};