//  Created by Steve on 12/7/10.
//  Copyright 2010 Steve McFarlin. All rights reserved.
//  Licensing at bottom of file.

// Modifications by Martin Oehler <netyoapp@netyo.tv> '2011-2013
// License: MIT License
// Remark: this file is open sourced to comply with MIT License

// netyo is a registered Trademark of TECHNO ET CONTROL (R) GMBH & CO KG

#include "ffstream.h"

#include <QuartzCore/QuartzCore.h>

#include <ctype.h>
#include <string.h>
#include <math.h>
#include <stdlib.h>
#include <errno.h>
#include <limits.h>
#include <unistd.h>
#include <netinet/in.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <sys/time.h>
#include <sys/resource.h>

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <time.h>
#include <fcntl.h>
#include <time.h>

#include "libavformat/avformat.h"
#include "libavutil/avassert.h"
#include "libavutil/avstring.h"

#include "rtmp.h"
#include "log.h"

/* needed for usleep() */
#define _XOPEN_SOURCE 600

#pragma mark -
#pragma mark FF settings
#pragma mark -

static int verbose              = 0;
static int thread_count         = 1;

static int64_t start_time       = 0;
static int64_t timer_start;

static int frame_width          = 0;
static int frame_height         = 0;
static float aspect_ratio       = 0;

static int audio_sample_rate    = 44100;
static int64_t channel_layout   = 0;
static int audio_channels       = 1;

static float mux_preload        = 1.2;
static float mux_max_delay      = 1.5;

static char *output_format      = "flv";
static char *input_format       = "mov";
static bool cleanup = false;
static int streamingState       = 0;

#pragma mark -
#pragma mark Structures 
#pragma mark -

@implementation FFstreamBuffer
@end

struct AVInputStream;
typedef struct AVOutputStream {
    int         file_index;         // file index 
    int         index;              // stream index in the output file 
    int         source_index;       // AVInputStream index 
    AVStream    *st;                // stream in the output file
    int         frame_number;
    int64_t     sync_opts;          // output frame counter, could be changed to some true timestamp
    struct AVInputStream *sync_ist; // input stream to sync against
    
} AVOutputStream;

typedef struct AVInputStream {
    int file_index;
    int index;
    AVStream *st;

    int64_t     sample_index;        
    int64_t     start;              
    int64_t     next_pts;  
    int64_t     pts;       
} AVInputStream;

typedef struct AVInputFile {
    int eof_reached;      // true if eof reached
    int ist_index;        // index of first stream in ist_table
    int nb_streams;       // nb streams we are aware of
} AVInputFile;


static AVMetadata       *metadata;
static AVInputFile      *input_file;
static AVFormatContext  *input_context;
static AVFormatContext  *output_context;
static AVInputStream    *input_streams[4];
static AVOutputStream   *output_streams[4];
static int nb_streams_used = 0;

#pragma mark -
#pragma mark Control and messaging variables
#pragma mark -

static int ERROR_CRITICAL = 0;
static bool last_buffer = false;
static int stopStream = 0;
static int finishStream = 0;
static int exited = 0;

static NSMutableArray *queue = nil;

double_t start_stream_time = 0.0;
double_t end_stream_time = 0.0;
double_t delta_stream_time = 0.0;
int64_t buffer_bytes_sent = 0 ;

#pragma mark - 
#pragma mark Function protos
#pragma mark -

static bool next_input_file();
static int open_output(const char *filename);
static int open_output_streams(AVFormatContext *oc);
static int open_input(const char *filename);
static int read_input_format();
static int setup_outputs();
static int ffstream_exit(int ret);
static int stream();

static int min = 0;
static int max = 0;
static char basepath[300];
static char nextbuffer[300];
static char currentbuffer[300];
static char basepath_recording[300];
static char currentpath_recording[300];
static char killfile[300];
char tmp[40] = "";
NSFileManager *fileManager;

static NSString* recorderPath;
static bool record = false;

#pragma mark -
#pragma mark Error strings
#pragma mark -

#define kSIGPIPEError       @"The network connection has closed"
#define kStreamTimeout      @"The server connection has timeed out"
#define kInitialized        @"Stream initialized"
#define kInitializeError    @"Stream init failed"
#define kStarted            @"Streaming has started"
#define kStopped            @"The stream has stopped"
#define kStreamError        @"Error connecting to server."


// Handle sigpipe
void sigpipe_handler(int sig) {
    if (sig == SIGPIPE && ERROR_CRITICAL == 0) {
        ERROR_CRITICAL = 1;
        stopStream = 1;    
    }
}

static void init_sig_handlers(void) {
    signal(SIGPIPE , &sigpipe_handler); /* Interrupt (ANSI).  */
}

void togglerecord() {
    if( record == false )
        record = true;
    else
        record = false;
}

void ffstream_set_message_handler(FFstreamMessageHandler *handler) {
    // message_handler = handler;
}

void increase_filepath() {
    min++;
    strcpy(currentbuffer, basepath );
    sprintf( tmp, "%i.mov", min );
    strcat(currentbuffer, tmp );
    
    strcpy(nextbuffer, basepath );
    sprintf( tmp, "%i.mov", (min+1) );
    strcat(nextbuffer, tmp );
}

void rtmp_callback(int level, const char* str) {
    switch (level) {
        case RTMP_LOGCRIT:
            ERROR_CRITICAL = 1;
            stopStream = 1;
            [[NSNotificationCenter defaultCenter] postNotificationName:@"ffstreamerrorrtmpcallback" object:nil];
            break;
        default:
            break;
    }
}

void rtmp_custom_callback(int level, const char* str) {
    switch (level) {
        case RTMP_SOCK_FULL:
            fprintf(stderr, "Network stalled!");
            [[NSNotificationCenter defaultCenter] postNotificationName:@"ffstreamerror" object:nil];
            [[NSNotificationCenter defaultCenter] postNotificationName:@"ffstreamerrornetworkstalled" object:nil];
            streamingState = 3;
            break;
        case RTMP_SOCK_TIMEOUT:
            ERROR_CRITICAL = 1;
            stopStream = 1;
            fprintf(stderr, "The connection was lost!");
            streamingState = 3;
            [[NSNotificationCenter defaultCenter] postNotificationName:@"ffstreamerror" object:nil];
            [[NSNotificationCenter defaultCenter] postNotificationName:@"ffstreamerrorconnectionlost" object:nil];
            break;
        default:
            break;
    }
}

void ffstream_setmax( const int* newmax ) {
    max = *newmax;
}

void ffstream_setbasepath( const char* newbasepath ) {
    strcpy( basepath, newbasepath );
}

void ffstream_setrecorderpath( const char* newrecorderpath ) {
    strcpy( basepath_recording, newrecorderpath );
}

int getStreamingState() {
    int temp = streamingState;
    if( streamingState == 2 )
    streamingState = 1;
    return temp;
}

void ffstream_init_lib() {
    av_log_set_flags(AV_LOG_INFO);
    avcodec_register_all();
    av_register_all();
    av_log_set_level(AV_LOG_INFO);
    streamingState = 1;
    [[NSNotificationCenter defaultCenter] postNotificationName:@"ffstreaminit" object:nil];
    
    queue = [[NSMutableArray alloc] init];
    fileManager = [NSFileManager defaultManager];
    
    init_sig_handlers();
}

int ffstream_init(const char* url) {
    stopStream = 0;
    finishStream = 0;
    ERROR_CRITICAL = 0;
    last_buffer = false;
    stopStream = 0;
    nb_streams_used = 0;
    
    RTMP_LogSetExtCallback(rtmp_callback);
    RTMP_LogSetCustomCallback(rtmp_custom_callback);
    
    if ( !open_output(url) ) {
        stopStream = 1;
        return 0;
    }
    return 1;
}

void ffstream_start(int q_min) {
    
    int err = 0;
    exited = 0;
    
    if(!stopStream) {
        if (stopStream) {
            err = 1;
            goto end;
        }
        
        FFstreamBuffer *buffer = [queue objectAtIndex:0];
        if(!last_buffer &&
          open_input([buffer->bufferLink cStringUsingEncoding:NSASCIIStringEncoding]) &&
             read_input_format() &&
             open_output_streams(output_context) ) 
        {
           stream();
           err = 0;
        }
        else {
            err = 1;
        }
    }
end:
    ffstream_exit(err);
}

void tec_ffstream() {
    exited = 0;
    
    // this decrease is important since is ensures that the buffer search
    // starts at 0 and NOT at the last buffer count
    min = 0;
    
    // this is the initial "increase" to 0
    strcpy(currentbuffer, basepath );
    sprintf( tmp, "%i.mov", min );
    strcat(currentbuffer, tmp );
    
    strcpy(nextbuffer, basepath );
    sprintf( tmp, "%i.mov", (min+1) );
    strcat(nextbuffer, tmp );
    
    strcpy(killfile, basepath);
    sprintf( tmp, "killffstream.txt");
    strcat( killfile, tmp);
    
    while( !stopStream ) {
        // hang around until nextbuffer is ready
        
        while( ! [fileManager fileExistsAtPath:[NSString stringWithUTF8String:nextbuffer]]) {
            usleep( 1000 );
        }
        
        if( !stopStream ) {
            if( open_input(currentbuffer) &&
               read_input_format() &&
               open_output_streams(output_context) )
            {
                // NSLog(@"ffstream_start Before stream()");
                stream();
            }
            
            increase_filepath();
        }
    }
}

void ffstream_stop() {
    fprintf(stderr, "[ffstream] Stream stopped!!!\n");
    NSLog(@"[ffstream] Stream stopped!!!");
    stopStream = 1;
}

void ffstream_kill() {
    fprintf(stderr, "[ffstream] Stream connection stopped!\n");
    NSLog(@"[ffstream] Stream connection stopped!");
    ffstream_exit(1) ;
}

void ffstream_append_buffer(FFstreamBuffer *buffer) {
    if(exited || stopStream) return;
        
    last_buffer = buffer->last_buffer;
    @synchronized(queue) {
        [queue addObject:buffer];  
    } 
}

static int ffstream_exit(int ret)
{
    /* fprintf(stderr, "[ffstream] Stream connection stopped!\n");
    NSLog(@"[ffstream] Stream connection stopped!"); */
    
    if (exited) {
        return 1;
    }
    exited = 1;
    AVFormatContext *s = output_context;
    int j;
    if (s) {

        if (!(s->oformat->flags & AVFMT_NOFILE) && s->pb)
            url_fclose(s->pb);
        for(j=0;j<s->nb_streams;j++) {
            av_metadata_free(&s->streams[j]->metadata);
            if (s->streams[j]->codec->extradata) {
                av_free(s->streams[j]->codec->extradata) ;
            }
            av_free(s->streams[j]->codec);
            av_free(s->streams[j]->info);
            av_free(s->streams[j]);            
        }
        av_metadata_free(&s->metadata);
        av_free(s);
    }
    
    NSError *err;

        while ([queue count] > 0) {
            FFstreamBuffer *buffer = [queue objectAtIndex:0];
            if ( [fileManager fileExistsAtPath:buffer->bufferLink]) {
                BOOL success = [fileManager removeItemAtPath:buffer->bufferLink error:&err];
                if(!success) {
                }
            }
            [queue removeObjectAtIndex:0];
        }
    
    if(input_context)
        av_close_input_file(input_context);
    
    for(int i = 0; i < nb_streams_used;i++) {
        av_free(input_streams[i]);
        av_free(output_streams[i]);
    }
    
    output_context = NULL;
    input_context = NULL;
    return ret;
}


static int output_packet(AVInputStream *ist, AVOutputStream *ost, const AVPacket *pkt) {
    
    AVFormatContext *os;
    int ret;
    AVPacket avpkt;
    
    
    if(ist->next_pts == AV_NOPTS_VALUE)
        ist->next_pts= ist->pts;
    
    if (pkt == NULL) {
        /* EOF handling */
        av_init_packet(&avpkt);
        avpkt.data = NULL;
        avpkt.size = 0;
        return -1;
        
    } else {
        avpkt = *pkt;
    }
    
    if(pkt->dts != AV_NOPTS_VALUE) {
        ist->next_pts = ist->pts = av_rescale_q(pkt->dts, ist->st->time_base, AV_TIME_BASE_Q);
    }
        
    while ( (avpkt.size > 0 || (!pkt && ist->next_pts != ist->pts)) && !ERROR_CRITICAL) {
        ist->pts= ist->next_pts; 
        
        switch(ist->st->codec->codec_type) {
            case AVMEDIA_TYPE_AUDIO:
                ist->next_pts += ((int64_t)AV_TIME_BASE * ist->st->codec->frame_size) /
                ist->st->codec->sample_rate;
                break;
            case AVMEDIA_TYPE_VIDEO:
                if (ist->st->codec->time_base.num != 0) {
                    int ticks= ist->st->parser ? ist->st->parser->repeat_pict+1 : ist->st->codec->ticks_per_frame;
                    ist->next_pts += ((int64_t)AV_TIME_BASE * ist->st->codec->time_base.num * ticks) / ist->st->codec->time_base.den;
                }
                break;
            case AVMEDIA_TYPE_UNKNOWN:
                NSLog(@"MEDIA TYPE UNKNOWN!");
            case AVMEDIA_TYPE_DATA:
                NSLog(@"MEDIA TYPE UNKNOWN!");
            case AVMEDIA_TYPE_ATTACHMENT:
                NSLog(@"MEDIA TYPE UNKNOWN!");
            case AVMEDIA_TYPE_SUBTITLE:
                NSLog(@"MEDIA TYPE UNKNOWN!");
            case AVMEDIA_TYPE_NB:
                NSLog(@"MEDIA TYPE UNKNOWN!");
            
        }
        
            os = output_context;
            
            AVFrame avframe; 
            AVPacket opkt;
            int64_t ost_tb_start_time= av_rescale_q(start_time, AV_TIME_BASE_Q, ost->st->time_base);
            
            av_init_packet(&opkt);
            
            
            avcodec_get_frame_defaults(&avframe);
            ost->st->codec->coded_frame= &avframe;
            avframe.key_frame = pkt->flags & AV_PKT_FLAG_KEY;
            
            opkt.stream_index= ost->index;
        
            opkt.pts = av_rescale_q(pkt->pts, ist->st->time_base, ost->st->time_base) - ost_tb_start_time;
            opkt.dts = av_rescale_q(pkt->dts, ist->st->time_base, ost->st->time_base);                    
            opkt.dts -= ost_tb_start_time;
            opkt.duration = av_rescale_q(pkt->duration, ist->st->time_base, ost->st->time_base);
            opkt.flags= pkt->flags;
            
            opkt.data = avpkt.data;
            opkt.size = avpkt.size;
            
            buffer_bytes_sent += opkt.size ;
            
            ret= av_interleaved_write_frame(os, &opkt);
            streamingState = 2;
            
            if (ret == 1) {
                stopStream = 1;
            }
            
            ost->st->codec->frame_number++;
            ost->frame_number++;
            av_free_packet(&opkt);
        
        avpkt.size = 0;
    }

    if (pkt == NULL) {
         return -1;
    }
    
    return 0;
}

static int stream() 
{
    int ret = 0;
    AVOutputStream  *ost;
    AVInputStream   *ist;
    
    char error[1024];
    uint8_t no_packet[1] = {0};
    int no_packet_count = 0;
    
    setup_outputs();
            
    input_file= av_mallocz(sizeof(AVInputFile));
    
    if (!input_file) {
        goto fail;
    }
    
    input_file->nb_streams = input_context->nb_streams;

    nb_streams_used = input_context->nb_streams;    
    
    for(int i = 0; i < nb_streams_used; i++) {
        input_streams[i]->pts = input_streams[i]->next_pts = AV_NOPTS_VALUE;
    }
    
    AVMetadataTag *t = NULL;
    
    if( (t = av_metadata_get(input_context->metadata, "", t, AV_METADATA_IGNORE_SUFFIX)) ) {
        av_metadata_set2(&output_context->metadata, t->key, t->value, AV_METADATA_DONT_OVERWRITE);
    }
    
    if (av_write_header(output_context) < 0) {
        return 0;
    }

    if (ret) {
        fprintf(stderr, "%s\n", error);
        goto fail;
    }
    
    timer_start = av_gettime();
    
    for(int i = 0; i < nb_streams_used; i++) {
        input_streams[i]->start = av_gettime();
    }

    start_stream_time = CACurrentMediaTime();
    buffer_bytes_sent = 0 ;
    
    for(;!ERROR_CRITICAL;) {
        
        AVPacket pkt;

        if (input_file->eof_reached){
            
            end_stream_time = CACurrentMediaTime();
            
            if(next_input_file()){
                input_file->eof_reached = 0;
                input_file->nb_streams = input_context->nb_streams;
                start_stream_time = CACurrentMediaTime();
                
                continue;
            }
            else {
                break;
            }
            
            break;
        }
        
        ret= av_read_frame(input_context, &pkt);
        
        
        if(ret == AVERROR(EAGAIN)){
            no_packet_count++;
            continue;
        }
        if (ret < 0) {
            input_file->eof_reached = 1;
            continue;
        }
        
        no_packet_count=0;
        memset(no_packet, 0, sizeof(no_packet));
        
        if (0) {
            av_pkt_dump_log(NULL, AV_LOG_DEBUG, &pkt, 1);
        }
        
        if (pkt.stream_index >= input_file->nb_streams)
            goto discard_packet;
        
        ist = input_streams[pkt.stream_index];
        ost = output_streams[pkt.stream_index];

        start_stream_time = CACurrentMediaTime();
        
        if (output_packet(ist, ost, &pkt) < 0) {
            av_free_packet(&pkt);
            continue;
        }
        delta_stream_time += CACurrentMediaTime() - start_stream_time;
        
    discard_packet:
        av_free_packet(&pkt);
    }
    
    if (!stopStream && last_buffer) {
        sleep(10);
    }
    
fail:
    av_free(input_file);
    return ret;
}


#pragma mark -
#pragma mark Input Output File Handling
#pragma mark -



static bool next_input_file() {
   
    NSError *err;
    FFstreamBuffer *buffer;
    double_t bit_rate = 0.0 ;
    
    av_close_input_file(input_context);
    input_context = 0;
    
    while( ! [fileManager fileExistsAtPath:[NSString stringWithUTF8String:nextbuffer]]) {
        usleep( 1000 );
        if( [fileManager fileExistsAtPath:[NSString stringWithUTF8String:killfile]] ) {
            stopStream = 1;
            return 0;
        }
    }
  
   if ( [fileManager fileExistsAtPath:[NSString stringWithUTF8String:currentbuffer]] ) {
       bool success = false;
       
       if( record == false ) {
           success = [fileManager removeItemAtPath:[NSString stringWithUTF8String:currentbuffer] error:&err];
       } else {
           // save to recorder directory
           strcpy(currentpath_recording, basepath_recording);
           sprintf( tmp, "%s", [[[NSString stringWithUTF8String:currentbuffer] lastPathComponent] UTF8String] );
           strcat(currentpath_recording, tmp);
           success = [fileManager moveItemAtPath:[NSString stringWithUTF8String:currentbuffer]
                                          toPath:[NSString stringWithUTF8String:currentpath_recording] error:&err];
       }
       increase_filepath();   
    }
    
    while( ! [fileManager fileExistsAtPath:[NSString stringWithUTF8String:nextbuffer]]) {
        usleep( 1000 );
        if( [fileManager fileExistsAtPath:[NSString stringWithUTF8String:killfile]] ) {
            stopStream=1;
            return 0;
        }
    }
    // release file manager
  
    bit_rate = (buffer_bytes_sent * 8) / delta_stream_time ;
    delta_stream_time = 0.0;
    buffer_bytes_sent = 0;
    
    if (ERROR_CRITICAL) { NSLog(@"ERROR CRITICAL"); return 0; }
    
    nb_streams_used = 0;
    if( open_input( currentbuffer) && read_input_format() ) {
        cleanup = true;
        for(int i = 0; i < nb_streams_used; i++) {

            input_streams[i]->st = input_context->streams[i];
        }
    }
    else {
        printf("[ffstream] Error opening buffer %s\n", currentbuffer );
        return 0;
    }
    return 1;
}

static int setup_outputs() {
    AVCodecContext *ocodec, *icodec;
    
    for(int i = 0;i < input_context->nb_streams; i++) {
        AVStream *ist = input_streams[i]->st;
        AVStream *ost = output_streams[i]->st;
        icodec = ist->codec;
        ocodec = ost->codec;
            
        ost->disposition = ist->disposition;
        ocodec->bits_per_raw_sample = icodec->bits_per_raw_sample;
        ocodec->chroma_sample_location = icodec->chroma_sample_location;
        
        uint64_t extra_size = (uint64_t)icodec->extradata_size + FF_INPUT_BUFFER_PADDING_SIZE;
        if (extra_size >= INT_MAX) {extra_size = 0;}
        
        ocodec->codec_id    = icodec->codec_id;
        ocodec->codec_type  = icodec->codec_type;
        ocodec->bit_rate    = icodec->bit_rate;
        ocodec->rc_max_rate = icodec->rc_max_rate;
        ocodec->rc_buffer_size = icodec->rc_buffer_size;
        ocodec->extradata   = av_mallocz(extra_size);
        if(!ocodec->extradata) {
            NSLog(@"Error allocating extra data");
            return 0;
        }
        
        memcpy(ocodec->extradata, icodec->extradata, icodec->extradata_size);
        ocodec->extradata_size  = icodec->extradata_size;
        ocodec->time_base       = ist->time_base;    
        
        switch (icodec->codec_type) {
            case AVMEDIA_TYPE_AUDIO:
                ocodec->channel_layout  = icodec->channel_layout;
                ocodec->sample_rate     = icodec->sample_rate;
                ocodec->channels        = icodec->channels;
                ocodec->frame_size      = icodec->frame_size;
                ocodec->block_align     = icodec->block_align;
                ocodec->sample_fmt      = icodec->sample_fmt;
                break;
            case AVMEDIA_TYPE_VIDEO:
                ocodec->pix_fmt = icodec->pix_fmt;
                ocodec->width   = icodec->width;
                ocodec->height  = icodec->height;
                ocodec->has_b_frames = icodec->has_b_frames;
                break;
            default:
                abort();
        }
    }    
    return 1;
}

static int open_input(const char *filename)
{
    AVFormatContext *fc;
    AVInputFormat *file_format = NULL;
    int err;
    
    if (!(file_format = av_find_input_format(input_format))) {
        
        NSLog( @"[ffstream] Error configuring media input type");
        return 0;
    }
 
    if (input_context) {
        fc = input_context;
    }
    else {
        fc = avformat_alloc_context();
    }

    if (!fc) {
        NSLog( @"[ffstream] Error allocating input context");
        return 0;
    }
 
    err = av_open_input_file(&fc, filename, NULL, 0, NULL);
 
    if (err < 0) {
        return 0;
    }
 
    input_context = fc;
    
    return 1;
}

static int read_input_format()
{
    int i;
    AVInputStream *is;
    
    int ret = av_find_stream_info(input_context);

    if (ret < 0 && verbose >= 0) {
        av_close_input_file(input_context);
        return 0;
    }
    
    int j = 0;

    for(i = 0;i < input_context->nb_streams; i++) {
        AVStream *st = input_context->streams[i];
        AVCodecContext *dec = st->codec;
        avcodec_thread_init(dec, thread_count);

        switch (dec->codec_type) {
            case AVMEDIA_TYPE_AUDIO:
                fprintf(stderr, "\nInput Audio channels: %d", dec->channels);
                channel_layout    = dec->channel_layout;
                audio_channels    = dec->channels;
                audio_sample_rate = dec->sample_rate;
                is = av_mallocz(sizeof(AVInputStream));
                if(!is) {
                    fprintf(stderr, "Could not alloc audio input stream\n");
                    return 0;
                }
                is->index = j;
                is->st = input_context->streams[i];
                
                input_streams[j++] = is;
                nb_streams_used++;
                break;
            case AVMEDIA_TYPE_VIDEO:
                frame_height = dec->height;
                frame_width  = dec->width;
                if(input_context->streams[i]->sample_aspect_ratio.num)
                    aspect_ratio = av_q2d(input_context->streams[i]->sample_aspect_ratio);
                else
                    aspect_ratio = av_q2d(dec->sample_aspect_ratio);
                aspect_ratio *= (float) dec->width / dec->height;
                
                is = av_mallocz(sizeof(AVInputStream));
                if(!is) {
                    fprintf(stderr, "Could not alloc video input stream\n");
                    return 0;
                }
                is->index = j;
                is->st = input_context->streams[i];
                
                input_streams[j++] = is;
                nb_streams_used++;
                break;
            case AVMEDIA_TYPE_DATA: break;
            case AVMEDIA_TYPE_SUBTITLE: break;
            case AVMEDIA_TYPE_ATTACHMENT:
            case AVMEDIA_TYPE_UNKNOWN: break;
            default:
                NSLog(@"Calling abort()\n");
                abort();
        } 
    }
    
    dump_format(input_context, 1, "", 0);
    
    return 1;
}

static int open_output(const char *filename)
{
    AVFormatContext *fc;
    int err;
    AVOutputFormat *file_format;
    AVMetadataTag *tag = NULL;
    
#ifdef DEBUG
    NSLog(@"[ffstream] Connection URL= %s", filename);
#endif
    
    fc = avformat_alloc_context();
    if (!fc) {
        fprintf(stderr, "[ffstream] Error allocating output context\n");
        return 0;
    }
    
    file_format = guess_format(output_format, NULL, NULL);
    //file_format = guess_stream_format(output_format, NULL, NULL);
    if (!file_format) {
        fprintf(stderr, "[ffstream] Error determining output format\n");
        return 0;
    }

    fc->oformat = file_format;
    NSLog(@"filename=%s", filename);
    if((sizeof(filename) == 0) || (strcmp(filename, "") == 0) ||  (strcmp(filename, " ") == 0))
        return 0;
    
    NSLog(@"filename=.%s.\n", filename );
    av_strlcpy(fc->filename, filename, sizeof(fc->filename));
    
    fc->timestamp = 0;
    
    while ((tag = av_metadata_get(metadata, "", tag, AV_METADATA_IGNORE_SUFFIX)))
        av_metadata_set2(&fc->metadata, tag->key, tag->value, 0);
    av_metadata_free(&metadata);
    
    fprintf(stderr, "[ffstream] Connecting to server...\n");
    NSLog(@"[ffstream] Connecting to server...\n");
    /* open the file */
    if ((err = url_fopen(&fc->pb, filename, URL_WRONLY)) < 0) {
        return 0; 
    }
    
    fc->preload = (int)(mux_preload*AV_TIME_BASE);
    fc->max_delay = (int)(mux_max_delay*AV_TIME_BASE);
    fc->flags |= AVFMT_FLAG_NONBLOCK;
    
    output_context = fc;
    return 1;
}


static int open_output_streams(AVFormatContext *oc)
{
    int j = 0;
    for(int i = 0;i < input_context->nb_streams; i++) {
        AVOutputStream *ost;
        AVStream *st = input_context->streams[i];
        AVCodecContext *dec = st->codec;
        avcodec_thread_init(dec, thread_count);
        
        
        switch (dec->codec_type) {
            case AVMEDIA_TYPE_AUDIO:
                st = av_new_stream(oc, 0);
                if (!st) {
                    fprintf(stderr, "[ffstream] Could not alloc audio stream\n");
                    return 0;
                }
                ost = av_mallocz(sizeof(AVOutputStream));
                if (!ost) {
                    fprintf(stderr, "[ffstream] Could not alloc audio output stream\n");
                    return 0;
                }
                
                avcodec_thread_init(st->codec, thread_count);
                st->stream_copy = 1;
                st->codec->codec_type = AVMEDIA_TYPE_AUDIO;
                st->codec->flags |= CODEC_FLAG_GLOBAL_HEADER;
                st->codec->channels = audio_channels;
                st->codec->sample_rate = audio_sample_rate;
                st->codec->time_base= (AVRational){1, audio_sample_rate};
                ost->st = st;
                ost->index = j;
                output_streams[j++] = ost;
                break;
            case AVMEDIA_TYPE_VIDEO:
                st = av_new_stream(oc, 0);
                if (!st) {
                    fprintf(stderr, "[ffstream] Could not alloc video stream\n");
                    return 0;
                }
                ost = av_mallocz(sizeof(AVOutputStream));
                if (!ost) {
                    fprintf(stderr, "[ffstream] Could not alloc video output stream\n");
                    return 0;
                }
                
                avcodec_thread_init(st->codec, thread_count);
                st->stream_copy = 1;
                st->codec->flags |= CODEC_FLAG_GLOBAL_HEADER;
                st->codec->codec_type = AVMEDIA_TYPE_VIDEO;
                st->codec->sample_aspect_ratio =
                st->sample_aspect_ratio = av_d2q(aspect_ratio*frame_height/frame_width, 255);
                
                ost->index = input_streams[j]->index;
                ost->source_index = input_streams[j]->index;
                ost->st = st;
                output_streams[j++] = ost;
                break;
            case AVMEDIA_TYPE_DATA: break;
            case AVMEDIA_TYPE_SUBTITLE: break;
            case AVMEDIA_TYPE_ATTACHMENT:
            case AVMEDIA_TYPE_UNKNOWN: break;
            default:
                abort();
        }
    }
    
    return 1;
}

/*
 The MIT License
 
 Copyright (c) 2010 Steve McFarlin
 
 Permission is hereby granted, free of charge, to any person obtaining a copy
 of this software and associated documentation files (the "Software"), to deal
 in the Software without restriction, including without limitation the rights
 to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 copies of the Software, and to permit persons to whom the Software is
 furnished to do so, subject to the following conditions:
 
 The above copyright notice and this permission notice shall be included in
 all copies or substantial portions of the Software.
 
 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 THE SOFTWARE.
 
 */
