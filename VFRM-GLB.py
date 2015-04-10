#!/usr/bin/python

import sys, os
import re, shutil
import linecache
import getopt
import operator
import copy
from collections import deque
import math
import heapq





class g:
   """
   Global variables & initialization.
   """
   FLASH_SIZE = 0    # flash size in MB (1MB = 2048 Blocks)
   BIN_SIZE = 2048   # bin size in blocks
   NUM_BIN = 0       # number of bin in flash
   REPLACE_EPOCH = 300     # bin replace interval in seconds
   WARMUP = 86400    # seconds, the traces in the first # seconds is used for flash training & warm-up:

   cache = None      # instance of Cache class
   numWL = 1
   wl = []           # workload: I/O trace from input files
   dirName = None    # input-file name without extention (.cvs)
   dirPath = None    # folder path for tier simulation results
   outPrefix = ''    # prefix for the output files

   glbBinCurrPop = dict()   # popularity statistic for bin access in current epoch
   glbBinCurrPrevPop = dict()   # yang: 20150219
   glbBinOldPop = dict()    # popularity records for bins in each old epochs
   glbBinNextPop = dict()   # predict popularity of each bin for the next epoch
   glbBinNextPopPrv = dict () # yang
   glbBinNextPopPub = dict () # yang
   numOldEpoch = 8     # number of history epochs in record
   epochWeight = [float(numOldEpoch-i)/numOldEpoch for i in xrange(numOldEpoch)]

   # YANG
   ################################################################################
   # INITILIZATION                                                                #
   ################################################################################

   ################################################################################
   # EVICT                                                                        # 
   ################################################################################
   prevPubEvictHistory = dict() # history of evicted bins from pub zone
   prevPrvEvictHistory = dict() # history of evicted bins from prv zone
   curPubEvictHistory  = dict()  # history of evicted bins from pub zone
   curPrvEvictHistory  = dict()  # history of evicted bins from prv zone
   overtimePubEvictHistory = dict()
   overtimePrvEvictHistory = dict()
   #NUM_PUBEVICTHISTORY=0
   #NUM_PRVEVICTHISTORY=0
   
   prvEvict=set()
   pubEvict=set()

   prvDup=set()
   pubDup=set()

   prvDupWithHistory=set()
   pubDupWithHistory=set()   
 
   ################################################################################
   # TRACE                                                                        # 
   ################################################################################
   ## PUBLIC

   # recent zero
   traceReuseDegreeCurrEpoch=0.0


   # recent one
   tracePubDupNum           = 0.0 # (pubDupNum)         yang 20150313
   tracePubDupRatio         = 0.0 # (pubReuseDegree)
   prevTracePubDupRatio     = 0.0 # (prevPubReuseDegree)yang 20150313

   # recent two
   prevTracePubDupNum       = 0.0 # (prevPubDupNum)yang 20150313
   tracePubDupDiffNum       = 0   # (pubDupDiffNum)yang 20150324
   tracePubDupDiffRatio     = 0.0 # (pubDupDiffRatio)yang 20150401

   # recent inf
   traceReuseDegreeAllEpoches=0.0

  
   ## PRIVATE 20150320
   # recent one
   tracePrvDupNum         = 0
   prevTracePrvDupNum     = 0
  
   # recent two
   tracePrvDupDiffNum     = 0
   tracePrvDupDiffRatio   = 0.0
   prevTracePrvDupDiffNum = 0
   prevGlbBinCountTopK    = {}




   ################################################################################
   # CACHE                                                                        #
   ################################################################################


   # yang 20150317


   # private
   hitInPrvBinNumCurrEpoch = {}
   hitInPrvZoneWorksetSizeCurrEpoch         = 0
   hitInPrvZoneWorksetSizePrevEpoch         = 0
   hitInPrvZoneWorksetSizeDiff              = 0
   hitInPrvZoneBinReuseDegreeCurrEpoch      = 0
   hitInPrvZoneAccessSizeCurrEpoch          = 0

   # public
   hitInPubBinNumCurrEpoch = {}
   hitInPubZoneWorksetSizeCurrEpoch         = 0
   hitInPubZoneWorksetSizePrevEpoch         = 0
   hitInPubZoneWorksetSizeDiff              = 0
   hitInPubZoneBinReuseDegreeCurrEpoch      = 0
   hitInPubZoneAccessSizeCurrEpoch          = 0

   ################################################################################
   ################################################################################   
      

   glbPolicy = 0        # global flash policy ID
   NUM_PUBLIC_BIN = 0   # total number of bins publicly shared by all workloads for recency
   NUM_PRIVATE_BIN = 0  # total number of bins reserved by all workloads for private reservation or frequency
   NEXT_NUM_PRIVATE_BIN=0 # yang
   NEXT_NUM_PUBLIC_BIN=0  # yang
   prvZoneRatio=0 #yang 20150222

   pubQue = {}          # public queue for the shared bins of all workloads used for recency
   prvQue = {}          # private queue reserved for all workloads userd for private reservation or frequency
   entireCahce = {}     # yang, pubQue+prvQue
   glbBinCount = {}     # access counting for each global bin
   glbBinCountPrev = {} # yang, 20150318
   MAX_BIN_COUNT = 1000000000    # max access number for each global bin

   writePolicy = 0      # numeric code for write policy
   wrAbbr = None        # abbreviation of write policy
   IO_SIZE = 256        # IO size in blocks
   NUM_IO_PER_BIN = BIN_SIZE / IO_SIZE
   # I/O cost for exchange data between SSD & MD
   numAdmin = 0         # number of cache admission (migrate data from MD to SSD)
   numEvict = 0         # number of cache eviction (migrate data from SSD out to MD)
   numBypass = 0        # number of both Read/Write I/O bypass cache and directly access MD
   numSsdRead = 0
   numSsdWrite = 0
   numMdRead = 0
   numMdWrite = 0


class Workload:
   def __init__(self):
      self.inFile = None     # input file path for this workload class
      self.fname = None      # input file name (not abspath)
      self.curLine = 1       # current line number in trace file
      self.lastLine = False  # flag for reading the last trace in each input file
      self.ioRW = 0       # reference for Read/Write flag
      self.ioLBN = 0      # reference for I/O logical block number (LBN)
      self.ioSize = 0     # reference for I/O size, number of blocks
      self.ioTime = 0     # reference for I/O access time
      self.timeOffset = 0   # time offset for each trace starting from 0
      self.timeLength = 0   # total time duration for the whole trace in this workload
      self.binCurrPop = dict()   # dict for popularity statistic of bins in current epoch
      self.numPrvBin = 0      # minimal number of bins assigned to this workload
      self.prvQue = {}

      self.numIO = 0       # number I/O in workload
      self.numRead = 0
      self.numWrite = 0
      self.numIOFlash = 0     # number of I/O bypassed flash
      self.numHit = 0
      self.numReadFlash = 0
      self.numWriteFlash = 0
      self.numIOEpoch = 0     # number of I/O in an epoch
      self.numHitEpoch = 0
      #self.hitInPrvBinNumCurrEpoch = 0 # yang 20150317
      #self.hitInPubBinNumCurrEpoch = 0 # yang 20150317
      #self.numHitInPrvEpoch = 0  #yang
      #self.numHitInPubEpoch = 0  #yang
      self.numReadEpoch= 0
      self.numWriteEpoch = 0


def Usage():
   print 'USAGE'
   print '\t%s [OPTIONS] <flash size(MB)> <trace files>\n' % (os.path.basename(sys.argv[0]))
   print 'OPTOIONS'
   print '\t-h, --help'
   print '\t\tPrint a usage message briefly summarizing the command-line options, then exit.'
   print '\t-e NUM, --epoch=NUM'
   print '\t\tFlash flush interval in NUM seconds.\n\t\tDefault is %d seconds.' % g.REPLACE_EPOCH
   print '\t-g NUM, --global=NUM'
   print '\t\tThe NUM-th global flash policy.\n\t\tDefault is global-%d policy.' % g.glbPolicy
   print '\t-w NUM, --write=NUM'
   print '\t\tThe flash write policy. \'0\' is Write Back and \'1\' is Write Through.\n\t\tDefault is Write Back.'
   print '\t-p PrefixName, --prefix=PrefixName'
   print '\t-z PrvZoneRatio, --prvZoneRatio=PrvZoneRatio'
   print '\t\tThe prefix for the output files.\n\t\tWithout specification, the default file name is created.'
   print '\n'
   sys.exit(1)


def main():
   # Check for arguments
   try:
      opts, args = getopt.getopt(sys.argv[1:], "he:g:w:p:z:", ["help", "epoch=", "global=", "write=", "prefix=","prvZoneRatio="])
   except getopt.GetoptError:
      Usage()
   if len(args) < 2:
      Usage()
   else:
      g.FLASH_SIZE = int(args[0])
      g.numWL = len(args) - 1;
      assert 0 < g.numWL <= 0xF
      g.wl = [Workload() for i in xrange(g.numWL)]
   for opt, arg in opts:
      if opt in ("-h", "--help"):
         Usage()
      elif opt in ("-e", "--epoch"):
         g.REPLACE_EPOCH = long(arg)
         print g.REPLACE_EPOCH
      elif opt in ("-g", "--global"):
         g.glbPolicy = int(arg)
         assert g.glbPolicy == 0 or g.glbPolicy == 1 or g.glbPolicy == 2 or g.glbPolicy == 3 or g.glbPolicy == 4
      elif opt in ("-w", "--write"):
         g.writePolicy = int(arg)
         assert g.writePolicy == 0 or g.writePolicy == 1
      elif opt in ("-p", "--prefix"):
         g.outPrefix = arg + '-'
      elif opt in ("-z", "--prvZoneRatio"): #prvZoneRatio yang 20150222
         g.prvZoneRatio = int(arg)
         print g.prvZoneRatio
      else:
         Usage()

   if g.numWL == 1:#single trace
      g.glbPolicy = 0

   if g.writePolicy == 0:
      g.wrAbbr = 'WB'
   elif g.writePolicy == 1:
      g.wrAbbr = 'WT'

   g.NUM_BIN = g.FLASH_SIZE * 2048 / g.BIN_SIZE
   g.cache = Cache()    # set instance of Cache class

   for i in xrange(g.numWL):
      g.wl[i].inFile = args[i+1]
      fp = os.path.abspath(args[i+1])
      fh, ft = os.path.split(fp)
      g.wl[i].fname = os.path.splitext(ft)[0]
      if g.glbPolicy == 1:
         g.wl[i].numPrvBin = int(g.NUM_BIN / g.numWL * g.prvZoneRatio/100)

   if g.glbPolicy == 1 or g.glbPolicy == 2:
      g.NUM_PRIVATE_BIN = int(round(g.NUM_BIN * g.prvZoneRatio/100))#size
      g.NUM_PUBLIC_BIN  = g.NUM_BIN - g.NUM_PRIVATE_BIN



   CreateFolder()

   # Initialize trace references
   for i in xrange(g.numWL):
      [g.wl[i].ioTime, g.wl[i].ioRW, g.wl[i].ioLBN, g.wl[i].ioSize] = GetTraceReference(g.wl[i].inFile, g.wl[i].curLine)
      if g.wl[i].ioLBN == 0:
         print 'Error: cannot get trace from the %dth trace file: %s' % (i, g.wl[i].inFile)
         sys.exit(1)
      g.wl[i].curLine += 1
      g.wl[i].timeOffset = g.wl[i].ioTime   # calculate time offset for the starting time of each trace
      g.wl[i].ioTime = 0
   # Get the latest trace
   curWL = GetNextWorkload()
   curEpoch = 1   # the number of flush epoch
   breakWLs = 0    # flag to break the "while", all the workloads have been done.

   # YANG INITILIZATION
   ################################################################################
   # TRACE
   ################################################################################
   # 20150222 yang print log
   g.prvDupWithHistoryLog   = file(str(str(g.outPrefix)+'evictPrvDupWithHistoryLog.txt'),'w',0)
   g.pubDupWithHistoryLog   = file(str(str(g.outPrefix)+'evictPubDupWithHistoryLog.txt'),'w',0)


   # 1. PUBLIC ZONE
   
   # 1.1 recent zero (current)
   # 1.1.1 workset size
   g.tracePubWorksetSizeCurrEpochLog   = file(str(str(g.outPrefix)+'tracePubWorksetSizeCurrEpochLog.txt'),  'w',0) 
   # 1.1.2 workset reuse degree
   g.tracePubReuseDegreeCurrEpochLog   = file(str(str(g.outPrefix)+'tracePubReuseDegreeCurrEpochLog.txt'),  'w',0)



   # 1.2 recent one (delta of current and previous)
   # 1.2.1 workset dup num
   g.tracePubDupNumLog    = file(str(str(g.outPrefix)+'tracePubDupNumLog.txt'),'w',0)
   # 1.2.2 workset dup ratio
   g.tracePubDupRatioLog  = file(str(str(g.outPrefix)+'tracePubDupRatioLog.txt'),'w',0)

   # 1.3 recent two (delta of delta)
   # 1.3.1 workset dup diff num
   g.tracePubDupDiffNumLog       = file(str(str(g.outPrefix)+'tracePubDupDiffNumLog.txt'),'w',0) # 20150324
   # 1.3.2 workset dup diff num
   g.tracePubDupDiffRatioLog     = file(str(str(g.outPrefix)+'tracePubDupDiffRatioLog.txt'),'w',0) #20150401

   # 1.4 recent inf (delta of current and all histroy)
   # 1.4.1 workset dup num in history
   g.traceReuseNumAllEpochesLog  = file(str(str(g.outPrefix)+'traceReuseNumAllEpochesLog.txt'), 'w',0)
   # 1.4.2 workset dup ratio in history
   g.traceReuseDegreeAllEpochesLog  = file(str(str(g.outPrefix)+'traceReuseDegreeAllEpochesLog.txt'), 'w',0)


   # 2. PRIVATE ZONE

   # 2.1 recent one 
   # 2.1.1 workset dup num
   g.tracePrvDupNumLog           = file(str(str(g.outPrefix)+'tracePrvDupNumLog.txt'),  'w',0)

   # 2.2 recent two
   # 2.2.1 workset dup diff num
   g.tracePrvDupDiffNumLog       = file(str(str(g.outPrefix)+'tracePrvDupDiffNumLog.txt'),  'w',0)
   # 2.2.2 workset dup diff ratio
   g.tracePrvDupDiffRatioLog     = file(str(str(g.outPrefix)+'tracePrvDupDiffRatioLog.txt'),  'w',0)



   #g.traceCurrPopLog  = file(str(str(g.outPrefix)+'traceCurrPopLog'),'w',0)
   ################################################################################
   # CACHE
   ################################################################################
   g.hitInPrvZoneWorksetSizeCurrEpochLog         = file(str(str(g.outPrefix)+'hitInPrvZoneWorksetSizeCurrEpochLog.txt'),   'w',0)
   g.hitInPrvZoneBinReuseDegreeCurrEpochLog      = file(str(str(g.outPrefix)+'hitInPrvZoneBinReuseDegreeCurrEpochLog.txt'),'w',0)
   g.hitInPrvZoneWorksetSizeDiffLog              = file(str(str(g.outPrefix)+'hitInPrvZoneWorksetSizeDiffLog.txt'),'w',0)

   g.hitInPubZoneWorksetSizeCurrEpochLog         = file(str(str(g.outPrefix)+'hitInPubZoneWorksetSizeCurrEpochLog.txt'),   'w',0)
   g.hitInPubZoneBinReuseDegreeCurrEpochLog      = file(str(str(g.outPrefix)+'hitInPubZoneBinReuseDegreeCurrEpochLog.txt'),'w',0)
   g.hitInPubZoneWorksetSizeDiffLog              = file(str(str(g.outPrefix)+'hitInPubZoneWorksetSizeDiffLog.txt'),'w',0)

   g.hitInPrvPubZoneAccessSizeLog                = file(str(str(g.outPrefix)+'hitInPrvPubZoneAccessSizeLog.txt'),'w',0)
   ################################################################################
   # RESIZE
   ################################################################################
   g.newPrvPubZoneSizeLog        = file(str(str(g.outPrefix)+'newPrvPubZoneSizeLog.txt'), 'w',0)

   ################################################################################
   ################################################################################




   # Main loop
   while True:
      # running progress record
      #g.traceCurrPopLog.write('#################################### START ####################################'+'\n')   
      if g.wl[curWL].curLine % 100000 == 0:
         print '%s:\t%d' % (g.wl[curWL].inFile, g.wl[curWL].curLine)

      startBinID = g.wl[curWL].ioLBN / g.BIN_SIZE
      binNum = (g.wl[curWL].ioLBN + g.wl[curWL].ioSize - 1) / g.BIN_SIZE - startBinID + 1

     

      if g.wl[curWL].ioTime < curEpoch * g.REPLACE_EPOCH:
         PopStatCurrEpoch(startBinID, binNum, curWL)
         WorkloadStat(curWL)
         if curEpoch * g.REPLACE_EPOCH > g.WARMUP:
            #print '==a=='
            flag = CheckCacheHit(g.wl[curWL].ioLBN, g.wl[curWL].ioSize, g.wl[curWL].ioRW, curWL)  # check cache hit
            WorkloadStatInFlash(curWL, flag)
      else:
         numGap = g.wl[curWL].ioTime / g.REPLACE_EPOCH - curEpoch + 1
#         strEpoch = curEpoch * g.REPLACE_EPOCH
#         endEpoch = (curEpoch + numGap) * g.REPLACE_EPOCH

         StatByEpoch(curEpoch, numGap)
         #g.traceCurrPopLog.write('#################################### START ####################################'+'\n')   
         PopRecordByEpoch()
         PopPredNextEpoch()
         g.cache.FlushBin()  # update cached bins
         if g.numWL > 1:
            GetFlashShare(curEpoch, numGap)
         ClearStatCurrEpoch()

         curEpoch += numGap
#         g.wl[curWL].curLine -= 1
         continue
      #g.traceCurrPopLog.write('#################################### END ####################################'+'\n')  






      # Get trace reference
      [g.wl[curWL].ioTime, g.wl[curWL].ioRW, g.wl[curWL].ioLBN, g.wl[curWL].ioSize] = GetTraceReference(g.wl[curWL].inFile, g.wl[curWL].curLine)
      g.wl[curWL].ioTime -= g.wl[curWL].timeOffset
      if g.wl[curWL].ioLBN == 0:
         g.wl[curWL].lastLine = True
         breakWLs += 1
         g.wl[curWL].timeLength = (GetTraceReference(g.wl[curWL].inFile, g.wl[curWL].curLine-1)[0] - g.wl[curWL].timeOffset) / float(3600)
         if breakWLs == g.numWL:
            break
      g.wl[curWL].curLine += 1
      curWL = GetNextWorkload()
   #while end

   StatByEpoch(curEpoch, 1)
   ClearStatCurrEpoch()
   # Display results of program run
   PrintSummary()
   g.prvDupWithHistoryLog.close()
   g.pubDupWithHistoryLog.close()
   #g.prvDupWithLastEpochLog.close() 
   #g.pubDupWithLastEpochLog.close()


def GetNextWorkload():
   j = None
   for i in xrange(g.numWL):
      if not g.wl[i].lastLine:
         minTime = g.wl[i].ioTime
         j = i
         break
   assert j is not None
   if (j+1) < g.numWL:
      for i in range(j+1, g.numWL):
         if not g.wl[i].lastLine and g.wl[i].ioTime < minTime:
            minTime = g.wl[i].ioTime
            j = i
   return j

def ClearStatCurrEpoch():

   #g.glbBinCurrPrevPop=g.glbBinCurrPop # 20150219 yang
   #g.glbBinCurrPrevPop=copy.deepcopy(g.glbBinCurrPop) # 20150224 yang


   g.glbBinCurrPop.clear()    # clear bin popularity records in last epoch
   g.glbBinNextPop.clear()
   g.glbBinNextPopPrv.clear() #yang
   g.glbBinNextPopPub.clear() #yang
   
   g.hitInPrvBinNumCurrEpoch.clear() #yang 20150317
   g.hitInPubBinNumCurrEpoch.clear() #yang 20150317

   for i in xrange(g.numWL):
      g.wl[i].binCurrPop.clear()
      g.wl[i].numIOEpoch = g.wl[i].numHitEpoch = g.wl[i].numHitInPrvEpoch = g.wl[i].numHitInPubEpoch = g.wl[i].numWriteEpoch = g.wl[i].numReadEpoch = 0


def StandardDeviation(q):
   mean = sum(q) / float(len(q))
   var = map(lambda x : math.pow(x-mean,2), q)
   sd = sum(var) / float(len(q))
   sd = math.sqrt(sd)
   cv = sd / mean
   return mean, sd, cv


def Welford_alg(mean, std, req, n):
   std  = std + pow(req - mean, 2) * (n - 1) / n
   mean = mean + (req - mean) / n
   return mean, std


def CheckCacheHit(ioLBN, ioSize, ioRW, wl):
   """
   Check cache hit.
   """
   #print '==b=='
   g.cache.numIO += 1
   if ioRW == 'R':
      g.cache.numRead += 1
   else:
      g.cache.numWrite += 1

   startIO = ioLBN / g.IO_SIZE
   numIO = (ioLBN + ioSize - 1) / g.IO_SIZE - startIO + 1
   lastBin = -1
   n = 0
   flagHit = True
   cacheHit = False
   for i in xrange(numIO):
      ioID = startIO + i
      binID = ioID / g.NUM_IO_PER_BIN
      binID = (binID << 4) + wl
      if binID == lastBin:
         n += 1
      else:
         IOCost(cacheHit, lastBin, ioRW, n)
         n = 1
         lastBin = binID
         cacheHit = g.cache.CheckHit(binID)
         if not cacheHit:
            flagHit = False
   IOCost(cacheHit, lastBin, ioRW, n)
   if flagHit:
      g.cache.numHit += 1
      ############## yang 20150302 ##################prvpub
      if g.cache.CheckHitInPrv(binID):
         g.cache.numHitInPrv+=1
         if binID in g.hitInPrvBinNumCurrEpoch:
            g.hitInPrvBinNumCurrEpoch[binID]+=1
         else:
            g.hitInPrvBinNumCurrEpoch[binID]=1
      
      elif g.cache.CheckHitInPub(binID):
         g.cache.numHitInPub+=1
         if binID in g.hitInPubBinNumCurrEpoch:
            g.hitInPubBinNumCurrEpoch[binID]+=1
         else:
            g.hitInPubBinNumCurrEpoch[binID]=1
      ###############################################
   return flagHit


def IOCost(cacheHit, binID, ioRW, n):
   if n != 0:
      if ioRW == 'R':
         if cacheHit:
            g.numSsdRead += n
         else:    #if read miss, directly read MD and bypass flash
            g.numMdRead += n
            g.numBypass += n
      elif ioRW == 'W' and g.writePolicy == 0:
         if cacheHit:
            g.numSsdWrite += n
            g.cache.SetDirty(binID)
         else:    #in write back, if write miss, directly write to MD w/o flash update
            g.numMdWrite += n
            g.numBypass += n
      elif ioRW == 'W' and g.writePolicy == 1:
         pass
#         if cacheHit:
#            g.numEvict += 1
#         else:    #in write back, if write miss, directly write to MD w/o flash update
#            g.numBypass += 1
      else:
         print 'Error: wrong write policy.'
         sys.exit(1)


def WorkloadStat(n):
   g.wl[n].numIO += 1
   g.wl[n].numIOEpoch += 1
   if g.wl[n].ioRW == 'W':
      g.wl[n].numWrite += 1
      g.wl[n].numWriteEpoch += 1
   else:
      g.wl[n].numRead += 1
      g.wl[n].numReadEpoch += 1

def WorkloadStatInFlash(n, flag): ###hitratio
   g.wl[n].numIOFlash += 1
   if g.wl[n].ioRW == 'W':
      g.wl[n].numWriteFlash += 1
   else:
      g.wl[n].numReadFlash += 1
   if flag:
      g.wl[n].numHit += 1
      g.wl[n].numHitEpoch += 1


def CreateFolder():
   filePath = os.path.abspath(sys.argv[0])
   fileHead, fileTail = os.path.split(filePath)
   if g.numWL == 1:
      fp = os.path.abspath(g.wl[0].inFile)
      fh, ft = os.path.split(fp)
      g.dirName = os.path.splitext(ft)[0]
   else:
      g.dirName = 'globalflash'
   g.dirPath = os.path.join(fileHead, 'cachesim-tier-' + g.dirName)
   if not os.path.isdir(g.dirPath):
      os.makedirs(g.dirPath)

   if g.numWL == 1:
      obj = os.path.join(g.dirPath, '%s-StatByEpoch-%dmin-%dMB' % (g.dirName, g.REPLACE_EPOCH/60, g.FLASH_SIZE))
      if os.path.isfile(obj):
         os.unlink(obj)
   else:
      for i in xrange(g.numWL):
         obj = os.path.join(g.dirPath, '%s-StatByEpoch-%dfile-%dmin-%dMB-glb%d' % (g.wl[i].fname, g.numWL, g.REPLACE_EPOCH/60, g.FLASH_SIZE, g.glbPolicy))
         if os.path.isfile(obj):
            os.unlink(obj)
      obj = os.path.join(g.dirPath, 'StatByEpoch-%dfile-%dmin-%dMB-glb%d' % (g.numWL, g.REPLACE_EPOCH/60, g.FLASH_SIZE, g.glbPolicy))
      if os.path.isfile(obj):
         os.unlink(obj)
      obj = os.path.join(g.dirPath, 'Flashshare-%dfile-%dmin-%dMB-glb%d' % (g.numWL, g.REPLACE_EPOCH/60, g.FLASH_SIZE, g.glbPolicy))
      if os.path.isfile(obj):
         os.unlink(obj)


def StatByEpoch(epoch, gap):
   """
   Calculate the effectiveness of cached bins.
   Effectiveness means the percentage of cached bins which are the bins in optimal case.
   """
   ################################################################################################################
   ############################################## Single Workload #################################################
   if g.numWL == 1:
      keyInCache = g.cache.binInCache.keys()
      keyInWL = g.wl[0].binCurrPop.keys()
      keyInst = set(keyInWL).intersection(set(keyInCache))
      hitRatio= float(g.wl[0].numHitEpoch) / g.wl[0].numIOEpoch * 100
      ######## yang ########################
      #hitNumInPrv=float(g.wl[0].numHitInPrvEpoch) #yang
      #hitNumInPub=float(g.wl[0].numHitInPubEpoch) #yang
      #hitRatioInPrv=float(g.wl[0].numHitInPrvEpoch) / g.wl[0].numIOEpoch * 100 #yang
      #hitRatioInPub=float(g.wl[0].numHitInPubEpoch) / g.wl[0].numIOEpoch * 100 #yang
      ######################################

      ###################[ StatByEpoch-8files-5min-3000MB-WB ]################### Single file
      with open(os.path.join(g.dirPath, '%sStatByEpoch-%s-%dmin-%dMB-%s' % (g.outPrefix, g.dirName, g.REPLACE_EPOCH/60, g.FLASH_SIZE, g.wrAbbr)), 'a') as source:
         #source.write('%d\t%d\t%d\t%d\t%d\t%.2f\t%d\t%d\t%d\t%d\t%d\%.2f\t%.2f\n' % (epoch*g.REPLACE_EPOCH/60, g.wl[0].numIOEpoch, g.wl[0].numReadEpoch, g.wl[0].numWriteEpoch, g.wl[0].numHitEpoch, hitRatio, len(keyInCache), len(keyInst), len(keyInWL), hitNumInPrv, hitNumInPub, hitRatioInPrv, hitRatioInPub)) #yang 20150227 #9+4=13
         source.write('%d\t%d\t%d\t%d\t%d\t%.2f\t%d\t%d\t%d\n' % (epoch*g.REPLACE_EPOCH/60, g.wl[0].numIOEpoch, g.wl[0].numReadEpoch, g.wl[0].numWriteEpoch, g.wl[0].numHitEpoch, hitRatio, len(keyInCache), len(keyInst), len(keyInWL))) #yang 20150227
         for j in xrange(gap-1):
            source.write('%d\t0\t0\t0\t0\t0.0\t%d\t0\t0\n' % ((epoch+1+j)*g.REPLACE_EPOCH/60, len(keyInCache))) # yang ignore, gap may be from the 5min boundry issue
   ################################################################################################################
   ############################################## Multiple Workloads ############################################## 
   else:
      cacheShare = [0 for i in xrange(g.numWL)]
      cachePct = [0.0 for i in xrange(g.numWL)]
      for key in g.cache.binInCache:
         key = key & 0xF
         assert 0 <= key < g.numWL
         cacheShare[key] += 1
      for i in xrange(g.numWL):
         cachePct[i] = float(cacheShare[i]) / g.NUM_BIN * 100

      if g.glbPolicy == 1 or g.glbPolicy == 2 or g.glbPolicy == 3 or g.glbPolicy == 4:
         rectShare = [0 for i in xrange(g.numWL)]
         rectPct = [0.0 for i in xrange(g.numWL)]
         for key in g.pubQue:
            key = key & 0xF
            rectShare[key] += 1
         for i in xrange(g.numWL):
            if g.NUM_PUBLIC_BIN==0:
               rectPct[i]=0
            else:
               rectPct[i] = float(rectShare[i]) / g.NUM_PUBLIC_BIN * 100

      if g.glbPolicy == 2 or g.glbPolicy == 3 or g.glbPolicy == 4:
         freqShare = [0 for i in xrange(g.numWL)]
         freqPct = [0.0 for i in xrange(g.numWL)]
         for key in g.prvQue:
            key = key & 0xF
            freqShare[key] += 1
         for i in xrange(g.numWL):
            freqPct[i] = float(freqShare[i]) / g.NUM_PRIVATE_BIN * 100

      ###################[ StatByEpoch-8files-5min-3000MB-WB-glb1 ]################### <= print hitratio of prvpubzone here
      with open(os.path.join(g.dirPath, '%sStatByEpoch-%dfile-%dmin-%dMB-%s-glb%d' % (g.outPrefix, g.numWL, g.REPLACE_EPOCH/60, g.FLASH_SIZE, g.wrAbbr, g.glbPolicy)), 'a') as source: #print stat of all files
         keyInCache = g.cache.binInCache.keys()
         source.write('Time = %d\tCache = %d\n' % (epoch*g.REPLACE_EPOCH/60, len(keyInCache)))
         #---------------------------------------
         for i in xrange(g.numWL):
            keyInWL = g.wl[i].binCurrPop.keys()
            keyInst = set(keyInWL).intersection(set(keyInCache))
            hitRatio = 0.0
            if g.wl[i].numIOEpoch != 0:
               hitRatio = float(g.wl[i].numHitEpoch) / g.wl[i].numIOEpoch * 100
            #------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
            ###################[ StatByEpoch-8files-5min-3000MB-WB-glb1-web_2 ]################### <=ignore
            with open(os.path.join(g.dirPath, '%sStatByEpoch-%dfile-%dmin-%dMB-%s-glb%d-%s' % (g.outPrefix, g.numWL, g.REPLACE_EPOCH/60, g.FLASH_SIZE, g.wrAbbr, g.glbPolicy, g.wl[i].fname)), 'a') as subSource: #print stat of each file
               if g.glbPolicy == 0:
                  subSource.write('%d\t%d\t%d\t%d\t%d\t%.2f\t%d\t%d\t%d\t%d\t%.2f\n' % (epoch*g.REPLACE_EPOCH/60, g.wl[i].numIOEpoch, g.wl[i].numReadEpoch, g.wl[i].numWriteEpoch, g.wl[i].numHitEpoch, hitRatio, len(keyInCache), len(keyInWL), len(keyInst), cacheShare[i], cachePct[i]))# yang ignore   
                  for j in xrange(gap-1):
                     subSource.write('%d\t0\t0\t0\t0\t0.0\t%d\t0\t0\t%d\t%.2f\n' % ((epoch+1+j)*g.REPLACE_EPOCH/60, len(keyInCache), cacheShare[i], cachePct[i])) # yang ignore


               elif g.glbPolicy == 1:
                  subSource.write('%d\t%d\t%d\t%d\t%d\t%.2f\t%d\t%d\t%d\t%d\t%.2f\t%d\t%d\t%.2f\n' % (epoch*g.REPLACE_EPOCH/60, g.wl[i].numIOEpoch, g.wl[i].numReadEpoch, g.wl[i].numWriteEpoch, g.wl[i].numHitEpoch, hitRatio, len(keyInCache), len(keyInWL), len(keyInst), cacheShare[i], cachePct[i], len(g.wl[i].prvQue), rectShare[i], rectPct[i]))#yang ignore
                  for j in xrange(gap-1):
                     subSource.write('%d\t0\t0\t0\t0\t0.0\t%d\t0\t0\t%d\t%.2f\t%d\t%d\t%.2f\n' % ((epoch+1+j)*g.REPLACE_EPOCH/60, len(keyInCache), cacheShare[i], cachePct[i], len(g.wl[i].prvQue), rectShare[i], rectPct[i])) #yang ignore


               elif g.glbPolicy == 2 or g.glbPolicy ==3:
                  subSource.write('%d\t%d\t%d\t%d\t%d\t%.2f\t%d\t%d\t%d\t%d\t%.2f\t%d\t%.2f\t%d\t%.2f\n' % (epoch*g.REPLACE_EPOCH/60, g.wl[i].numIOEpoch, g.wl[i].numReadEpoch, g.wl[i].numWriteEpoch, g.wl[i].numHitEpoch, hitRatio, len(keyInCache), len(keyInWL), len(keyInst), cacheShare[i], cachePct[i], freqShare[i], freqPct[i], rectShare[i], rectPct[i]))#yang ignore
                  for j in xrange(gap-1):
                     subSource.write('%d\t0\t0\t0\t0\t0.0\t%d\t0\t0\t%d\t%.2f\t%d\t%.2f\t%d\t%.2f\n' % ((epoch+1+j)*g.REPLACE_EPOCH/60, len(keyInCache), cacheShare[i], cachePct[i], freqShare[i], freqPct[i], rectShare[i], rectPct[i])) #yang ignore
            #------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
            if g.glbPolicy == 0:
               source.write('%s\t%d\t%d\t%d\t%.2f\t%d\t%d\t%.2f\n' % (g.wl[i].fname, len(keyInWL), len(keyInst), cacheShare[i], cachePct[i], g.wl[i].numIOEpoch, g.wl[i].numHitEpoch, hitRatio)) #yang ignore
            elif g.glbPolicy == 1:
               source.write('%s\t%d\t%d\t%d\t%.2f\t%d\t%d\t%.2f\t%d\t%d\t%.2f\n' % (g.wl[i].fname, len(keyInWL), len(keyInst), cacheShare[i], cachePct[i], len(g.wl[i].prvQue), rectShare[i], rectPct[i], g.wl[i].numIOEpoch, g.wl[i].numHitEpoch, hitRatio)) #yang ignore
            elif g.glbPolicy == 2 or g.glbPolicy ==3:
               source.write('%s\t%d\t%d\t%d\t%.2f\t%d\t%.2f\t%d\t%.2f\t%d\t%d\t%.2f\n' % (g.wl[i].fname, len(keyInWL), len(keyInst), cacheShare[i], cachePct[i], freqShare[i], freqPct[i], rectShare[i], rectPct[i], g.wl[i].numIOEpoch, g.wl[i].numHitEpoch, hitRatio)) #yang ignore
         source.write('\n')
         #---------------------------------------
         for j in xrange(gap-1):    # gaps for all the workloads #yang: useless
            source.write('Time = %d\tCache = %d\n' % ((epoch+1+j)*g.REPLACE_EPOCH/60, len(keyInCache)))
            for i in xrange(g.numWL):
               if g.glbPolicy == 0:
                  source.write('%s\t0\t0\t%d\t%.2f\t0\t0\t0.0\n' % (g.wl[i].fname, cacheShare[i], cachePct[i]))
               elif g.glbPolicy == 1:
                  source.write('%s\t0\t0\t%d\t%.2f\t%d\t%d\t%.2f\t0\t0\t0.0\n' % (g.wl[i].fname, cacheShare[i], cachePct[i], len(g.wl[i].prvQue), rectShare[i], rectPct[i]))
               elif g.glbPolicy == 2 or g.glbPolicy ==3:
                  source.write('%s\t0\t0\t%d\t%.2f\t%d\t%.2f\t%d\t%.2f\t0\t0\t0.0\n' % (g.wl[i].fname, cacheShare[i], cachePct[i], freqShare[i], freqPct[i], rectShare[i], rectPct[i]))
            source.write('\n')


      ###################[ StatByEpoch-8files-5min-3000MB-WB-glb1-PrvPubHitRatio ]################### <= print hitratio of prvpubzone here
      with open(os.path.join(g.dirPath, '%sStatByEpoch-%dfile-%dmin-%dMB-%s-glb%d-PrvPubHitRatio' % (g.outPrefix, g.numWL, g.REPLACE_EPOCH/60, g.FLASH_SIZE, g.wrAbbr, g.glbPolicy)), 'a') as PrvPubFile: #print stat of all files
         ###### yang 20150302 #################################################################################################
         if g.cache.numIO==0:
            HitRatio          = 0
            HitRatioInPrvZone = 0
            HitRatioInPubZone = 0
         else:
            HitRatio          = float(g.cache.numHit) / g.cache.numIO * 100
            HitRatioInPrvZone = float(g.cache.numHitInPrv) / g.cache.numIO * 100
            HitRatioInPubZone = float(g.cache.numHitInPub) / g.cache.numIO * 100
         IONum             = g.cache.numIO
         HitInPrvZoneNum   = g.cache.numHitInPrv
         HitInPubZoneNum   = g.cache.numHitInPub
         ######################################################################################################################
         PrvPubFile.write('%.4f%%\t%.4f%%\t%.4f%%\t%d\t%d\t%d\n' % (HitRatio, HitRatioInPrvZone, HitRatioInPubZone, IONum, HitInPrvZoneNum, HitInPubZoneNum)) #yang 







def GetFlashShare(epoch, gap):
   shares = [0.0 for i in xrange(g.numWL)]
   sharesInPrvZone = [0.0 for i in xrange(g.numWL)]
   sharesInPubZone = [0.0 for i in xrange(g.numWL)]
   sharePct = [0.0 for i in xrange(g.numWL)]
   sharePrvPct = [0.0 for i in xrange(g.numWL)]
   sharePubPct = [0.0 for i in xrange(g.numWL)]
   shareSum = [0.0 for i in xrange(g.numWL)]

   # binInCache
   for key in g.cache.binInCache: # key is WL id
      key = key & 0xF
      assert 0 <= key < g.numWL
      shares[key] += 1

   ########################################
   #################### 20150226 yang
   # binInPrvZone
   for key in g.cache.binInPrvZone: # key is WL id
      key = key & 0xF
      assert 0 <= key < g.numWL
      sharesInPrvZone[key] += 1
   # yang pubZone
   for key in g.cache.binInPubZone:
      key = key & 0xF
      assert 0 <= key < g.numWL
      sharesInPubZone[key] += 1
   ########################################
   ########################################

   sum = 0.0
   for i in xrange(g.numWL):
      sharePct[i] = float(shares[i]) / g.NUM_BIN * 100
      sharePrvPct[i] = float(sharesInPrvZone[i]) / g.NUM_BIN * 100 #yang
      sharePubPct[i] = float(sharesInPubZone[i]) / g.NUM_BIN * 100 #yang


      sum += sharePct[i]
      shareSum[i] = sum
   with open(os.path.join(g.dirPath, '%sFlashshare-%dfile-%dmin-%dMB-%s-glb%d' % (g.outPrefix, g.numWL, g.REPLACE_EPOCH/60, g.FLASH_SIZE, g.wrAbbr, g.glbPolicy)), 'a') as source:
      for i in xrange(gap):
         source.write('%d\t' % ((epoch+i)*g.REPLACE_EPOCH/60))
         for j in xrange(g.numWL):
            source.write('%.3f\t' % sharePct[j]) #yang sharePct is cache utilization ratio
         source.write('\n')

   ########################################
   #################### 20150226 yang
   with open(os.path.join(g.dirPath, '%sFlashsharePrvPub-%dfile-%dmin-%dMB-%s-glb%d' % (g.outPrefix, g.numWL, g.REPLACE_EPOCH/60, g.FLASH_SIZE, g.wrAbbr, g.glbPolicy)), 'a') as source:
      for i in xrange(gap):
         source.write('%d\t' % ((epoch+i)*g.REPLACE_EPOCH/60))
         for j in xrange(g.numWL):
            source.write('%.3f\t%.3f\t' % (sharePrvPct[j],sharePubPct[j])) #yang sharePct prv pub, cache utilization ratio
         source.write('\n')




def PopStatCurrEpoch(startBinID, binNum, n):
   """
   Bin popularity statistic in each epoch.
   """
   for i in xrange(binNum):
      binID = startBinID + i
      binID = (binID << 4) + n
      g.wl[n].binCurrPop[binID] = g.wl[n].binCurrPop.get(binID, 0) + 1
#      if binID in g.wl[n].binCurrPop:
#         g.wl[n].binCurrPop[binID] += 1 / float(binNum)
##         g.wl[n].binCurrPop[binID] += 1
#      else:
#         g.wl[n].binCurrPop[binID] = 1 / float(binNum)
##         g.wl[n].binCurrPop[binID] = 1

def ThrottleGlbBinCount():
   throttle = False
   for key in g.glbBinCount:
      if g.glbBinCount[key] >= g.MAX_BIN_COUNT:
         throttle = True
         break
   if throttle:
      for key in g.glbBinCount:
         g.glbBinCount[key] = int(math.log10(g.glbBinCount[key]))

def PopRecordByEpoch():
   """
   Update bin's popularity records of history epochs.
   Each bin maintains a list to record the history
   popularity for passed epochs. The length of list
   is equal to the number of history epochs need to
   be recorded.
   """
   # merge all the dict(s) of workloads to a global bin popularity dict
   for i in xrange(g.numWL):
      g.glbBinCurrPop.update(g.wl[i].binCurrPop) # glbBinCurrPop is cleared before

   for key in g.glbBinCurrPop:
      g.glbBinCount[key] = g.glbBinCount.get(key, 0) + g.glbBinCurrPop[key]
   ThrottleGlbBinCount()

   keyCurrEpoch = g.glbBinCurrPop.keys()
   keyOldEpochs = g.glbBinOldPop.keys()

   
   # yang 20150224

   ################################################################################
   ################################################################################
   # 1. TRACE  ####################################################################
   ################################################################################
   ################################################################################

   ################################################################################
   # 1.1 PUBLIC ZONE TRACE                                                        #
   ################################################################################

   #g.traceCurrPopLog.write('################################'+'\n')
   ## prevPop: g.glbBinCurrPrevPop
   #g.traceCurrPopLog.write('######## JZ-1 set(g.glbBinCurrPrevPop)='+str(len(set(g.glbBinCurrPrevPop)))+'='+str(set(g.glbBinCurrPrevPop))+'\n')   
   ## currPop: keyCurrEpoch
   #g.traceCurrPopLog.write('######## JZ-2 set(keyCurrEpoch)='       +str(len(set(keyCurrEpoch)))+'='+str(set(keyCurrEpoch))+'\n')   

   ## jianzhe
   keyInst = set(keyCurrEpoch).intersection(set(keyOldEpochs))  #key overlap
   keyCurrEpochDiff = set(keyCurrEpoch).difference(keyInst)     #keyCurrEpoch remainder
   keyOldEpochsDiff = set(keyOldEpochs).difference(keyInst)     #keyOldEpochs remainder


   ## yang: calculate duplication/overlapping
   prevCurrEpochInst=set(keyCurrEpoch).intersection(set(g.glbBinCurrPrevPop)) 
   # currPopDup: prevCurrEpochInst
   #g.traceCurrPopLog.write('######## JZ-3 set(prevCurrEpochInst)='+str(len(set(prevCurrEpochInst)))+'='+str(set(prevCurrEpochInst))+'\n')  

 
   #g.tracePubDupNumLog.write(str(len(prevCurrEpochInst))+'\n') #---------------------------------------------20150319


   g.glbBinCurrPrevPop=set(keyCurrEpoch)


   # 20150219
   ################################################################################
   # 1.1.1 recent zero (current)                                                  #
   ################################################################################
   # workset size
   g.tracePubWorksetSizeCurrEpochLog.write(str(len(g.glbBinCurrPop))+'\n')#20150401

   # reuse degree
   # glbBinCurrPop's sum divided by its workset
   g.tracePubReuseDegreeCurrEpoch=sum(g.glbBinCurrPop.values()) / float(len(g.glbBinCurrPop))
   g.tracePubReuseDegreeCurrEpochLog.write(str(g.tracePubReuseDegreeCurrEpoch)+'\n')



   ################################################################################
   # 1.1.2 recent one (delta of current and previous)                             #
   ################################################################################
   # workset dup num
   g.prevTracePubDupNum=g.tracePubDupNum # make a copy
   g.tracePubDupNum=len(prevCurrEpochInst)
   g.tracePubDupNumLog.write(str(g.tracePubDupNum)+'\n')
 
   # workset dup ratio
   g.prevTracePubDupRatio=g.tracePubDupRatio # make a copy
   g.tracePubDupRatio=float(len(prevCurrEpochInst)) / float(len(keyCurrEpoch))  
   g.tracePubDupRatioLog.write(str(g.tracePubDupRatio)+'\n')

   ################################################################################
   # 1.1.3 recent two (delta of delta)                                            #
   ################################################################################

   # workset dup diff num
   g.tracePubDupDiffNum=g.tracePubDupNum-g.prevTracePubDupNum 
   g.tracePubDupDiffNumLog.write(str(g.tracePubDupDiffNum)+'\n')

   # workset dup diff ratio
   if g.tracePubDupNum==0:
      g.tracePubDupDiffRatio=0
   else:
      g.tracePubDupDiffRatio=float(g.tracePubDupNum-g.prevTracePubDupNum)/g.tracePubDupNum
   g.tracePubDupDiffRatioLog.write(str(g.tracePubDupDiffRatio)+'\n')      


   ################################################################################
   # 1.1.4 recent inf (delta of current and all histroy)                          #
   ################################################################################
   # workset dup ratio in history
   g.traceReuseDegreeAllEpoches=float(len(set(keyCurrEpoch).intersection(set(g.glbBinCount)))) / float(len(keyCurrEpoch))
   g.traceReuseDegreeAllEpochesLog.write(str(g.traceReuseDegreeAllEpoches)+'\n')



   ################################################################################
   # 1.2 PRIVATE ZONE                                                             #
   # tracePrv   RECENT ONE                                                        #
   ################################################################################
   # yang 20150319 
   # make copy of previous status
   g.prevTracePrvDupNum     = g.tracePrvDupNum
   g.prevTracePrvDupDiffNum = g.tracePrvDupDiffNum
  
   # currDuplicationNum
   glbBinCountTopK=heapq.nlargest(int(g.NUM_BIN/2), g.glbBinCount.iteritems(), key=operator.itemgetter(1))
   glbBinCountTopK=[key[0] for key in glbBinCountTopK]
   
   g.tracePrvDupNum=len(set(glbBinCountTopK).intersection(g.prevGlbBinCountTopK))
   g.tracePrvDupNumLog.write(str(g.tracePrvDupNum)+'\n')                                     #---------------------------------------------20150319


   # diff
   # diffNum
   g.tracePrvDupDiffNum=g.tracePrvDupNum-g.prevTracePrvDupNum
   g.tracePrvDupDiffNumLog.write(str(g.tracePrvDupDiffNum)+'\n')                                   #---------------------------------------------20150319

   # diffRatio
   if g.tracePrvDupNum==0:
      g.tracePrvDupDiffRatio=0
   else:
      g.tracePrvDupDiffRatio=float(g.tracePrvDupNum-g.prevTracePrvDupNum)/g.tracePrvDupNum
   g.tracePrvDupDiffRatioLog.write(str(g.tracePrvDupDiffRatio)+'\n')                              #---------------------------------------------20150319   


   g.prevGlbBinCountTopK = glbBinCountTopK
  




   ################################################################################
   ################################################################################
   # 2. CACHE #####################################################################
   ################################################################################
   ################################################################################   

   # yang 20150317 hit in zone counter

   ################################################################################
   # 2.1 PRIVATE ZONE                                                             #
   ################################################################################

   # 2.1.1 Workset Num
   g.hitInPrvZoneWorksetSizePrevEpoch=g.hitInPrvZoneWorksetSizeCurrEpoch
   g.hitInPrvZoneWorksetSizeCurrEpoch=len(g.hitInPrvBinNumCurrEpoch)
   g.hitInPrvZoneWorksetSizeCurrEpochLog.write(str(g.hitInPrvZoneWorksetSizeCurrEpoch)+'\n')

   # 2.1.2 Reuse Degree
   g.hitInPrvZoneAccessSizeCurrEpoch=sum(g.hitInPrvBinNumCurrEpoch.values())
   if len(g.hitInPrvBinNumCurrEpoch)==0:
      g.hitInPrvZoneBinReuseDegreeCurrEpoch=0
   else:
      g.hitInPrvZoneBinReuseDegreeCurrEpoch = g.hitInPrvZoneAccessSizeCurrEpoch / float(len(g.hitInPrvBinNumCurrEpoch))
   g.hitInPrvZoneBinReuseDegreeCurrEpochLog.write(str(g.hitInPrvZoneBinReuseDegreeCurrEpoch)+'\n')
     
   # 2.1.3 Workset Diff Num
   g.hitInPrvZoneWorksetSizeDiff=g.hitInPrvZoneWorksetSizeCurrEpoch-g.hitInPrvZoneWorksetSizePrevEpoch
   g.hitInPrvZoneWorksetSizeDiffLog.write(str(g.hitInPrvZoneWorksetSizeDiff)+'\n')


   ################################################################################
   # 2.2 PUBLIC ZONE                                                              #
   ################################################################################


   # 2.2.1 Workset Num
   g.hitInPubZoneWorksetSizePrevEpoch=g.hitInPubZoneWorksetSizeCurrEpoch
   g.hitInPubZoneWorksetSizeCurrEpoch=len(g.hitInPubBinNumCurrEpoch)
   g.hitInPubZoneWorksetSizeCurrEpochLog.write(str(g.hitInPubZoneWorksetSizeCurrEpoch)+'\n')

   # 2.2.2 Reuse Degree
   g.hitInPubZoneAccessSizeCurrEpoch=sum(g.hitInPubBinNumCurrEpoch.values())
   if len(g.hitInPubBinNumCurrEpoch)==0:
      g.hitInPubZoneBinReuseDegreeCurrEpoch=0
   else:
      g.hitInPubZoneBinReuseDegreeCurrEpoch = g.hitInPubZoneAccessSizeCurrEpoch / float(len(g.hitInPubBinNumCurrEpoch))
   g.hitInPubZoneBinReuseDegreeCurrEpochLog.write(str(g.hitInPubZoneBinReuseDegreeCurrEpoch)+'\n')
     
   # 2.2.3 Workset Diff Num
   g.hitInPubZoneWorksetSizeDiff=g.hitInPubZoneWorksetSizeCurrEpoch-g.hitInPubZoneWorksetSizePrevEpoch
   g.hitInPubZoneWorksetSizeDiffLog.write(str(g.hitInPubZoneWorksetSizeDiff)+'\n')




   ################################################################################
   ################################################################################
   # 3. RESIZE ####################################################################
   ################################################################################
   ################################################################################

   ################################################################################ 
   # method1=classic
   newPrvSize1=0
   newPubSize1=0

   delta1=g.tracePrvDupDiffNum
   delta2=g.tracePubDupDiffNum 

   
   #if (g.NUM_PUBLIC_BIN+delta2)!=0:
   #   rhu1=(g.NUM_PRIVATE_BIN+delta1)/float(g.NUM_PUBLIC_BIN+delta2)
   #   if rhu1==0:
   #      rhu1=0.01
   #else:
   #   rhu1=0.99
   #newPrvSize1=int(g.NUM_BIN*rhu1/float(rhu1+1))

   newPubSize1=int(g.NUM_PUBLIC_BIN+1.5*delta2)
   if   newPubSize1>=int(0.99*g.NUM_BIN):
      newPubSize1=int(0.99*g.NUM_BIN)
   elif newPubSize1<=int(0.01*g.NUM_BIN):
      newPubSize1=int(0.01*g.NUM_BIN)

   newPrvSize1=g.NUM_BIN-newPubSize1
   
   ################################################################################
   # method2
   newPrvSize2=0
   newPubSize2=0

   # yang1
   #rhu=(g.tracePrvDupDiffNum+g.hitInPrvZoneAccessSizeCurrEpoch)/float(g.tracePubDupDiffNum + g.hitInPubZoneAccessSizeCurrEpoch +0.1)

   # yang2

   weightCacheHitAccessPrv=float(g.hitInPrvZoneAccessSizeCurrEpoch)/(g.hitInPrvZoneAccessSizeCurrEpoch+g.hitInPubZoneAccessSizeCurrEpoch+0.001)
   weightCacheHitAccessPub=float(g.hitInPubZoneAccessSizeCurrEpoch)/(g.hitInPrvZoneAccessSizeCurrEpoch+g.hitInPubZoneAccessSizeCurrEpoch+0.001)

   #rhu=(g.NUM_PRIVATE_BIN+g.tracePrvDupDiffNum*weightCacheHitAccessPrv)/float(g.NUM_PUBLIC_BIN+g.tracePubDupDiffNum*weightCacheHitAccessPub+0.01)

   # ningfang
   #rhu=(g.NUM_PRIVATE_BIN*weightCacheHitAccessPrv+g.tracePrvDupDiffNum)/float(g.NUM_PUBLIC_BIN*weightCacheHitAccessPub+g.tracePubDupDiffNum+0.01)
   #rhu=(g.NUM_BIN*weightCacheHitAccessPrv+g.tracePrvDupDiffNum)/float(g.NUM_BIN*weightCacheHitAccessPub+g.tracePubDupDiffNum+0.01)

   ################################################################################
   # Case 0. During warming up and ending stages, VFRM uses delta_pub
   ################################################################################
   if (g.hitInPrvZoneAccessSizeCurrEpoch==0 & g.hitInPubZoneAccessSizeCurrEpoch==0):# or ((g.hitInPrvZoneAccessSizeCurrEpoch==0 + g.hitInPubZoneAccessSizeCurrEpoch)<=int(1/20*g.NUM_BIN)):
      newPubSize2=int(g.NUM_PUBLIC_BIN+1.5*delta2)

   ################################################################################
   # Case 1. Bursty starts/ends: cache friendly, prv weitght low, 0.2*A1/A2
   # tracePubDiffNum <= 20% CacheSize
   ################################################################################
   #elif abs(g.tracePubDupDiffNum)>=int(g.NUM_BIN*0.20):
   # 0403 case A up going
   # aggressive
   elif (g.tracePubDupDiffRatio >= 0.7) or (g.tracePubDupDiffRatio <= -2):
      newPubSize2a=int(g.NUM_PUBLIC_BIN+1.5*delta2)
      rhu=0.4*float(g.hitInPrvZoneAccessSizeCurrEpoch)/(g.hitInPubZoneAccessSizeCurrEpoch+0.001)
      newPubSize2b=int(g.NUM_BIN/float(rhu+1))
      if newPubSize2a>=newPubSize2b:
         newPubSize2=newPubSize2a
      else:
         newPubSize2=newPubSize2b



   ################################################################################
   # Case 2. No bursty: cache unfriendly, prv weight high 0.4*A1/A2
   ################################################################################
   else:    
      rhu=0.4*float(g.hitInPrvZoneAccessSizeCurrEpoch)/(g.hitInPubZoneAccessSizeCurrEpoch+0.001)
      newPubSize2=int(g.NUM_BIN/float(rhu+1))
      
   g.hitInPrvPubZoneAccessSizeLog.write(str(g.hitInPrvZoneAccessSizeCurrEpoch)+'\t'+str(g.hitInPubZoneAccessSizeCurrEpoch)+'\n')
   if newPubSize2>=int(0.95*g.NUM_BIN):
      newPubSize2=int(0.95*g.NUM_BIN)
   elif newPubSize2<=int(0.01*g.NUM_BIN):
      newPubSize2=int(0.01*g.NUM_BIN)
      
   newPrvSize2=g.NUM_BIN-newPubSize2






   ################################################################################
   # RESIZE print resize log and assign new size                                  #
   ################################################################################
   g.newPrvPubZoneSizeLog.write(str(newPrvSize1)+'\t'+str(newPubSize1)+'\t'+str(newPrvSize2)+'\t'+str(newPubSize2)+'\n')

   # method1
   if g.glbPolicy==3:
      g.NUM_PRIVATE_BIN = newPrvSize1
      g.NUM_PUBLIC_BIN  = newPubSize1

   # method2
   if g.glbPolicy==2:#
      g.NUM_PRIVATE_BIN = newPrvSize2
      g.NUM_PUBLIC_BIN  = newPubSize2




   ################################################################################
   ################################################################################
   ################################################################################
   ################################################################################
   # there is access for this bin in last epoch
   for key in keyInst:
      if len(g.glbBinOldPop[key]) == g.numOldEpoch:
         del g.glbBinOldPop[key][0]
      g.glbBinOldPop[key].append(g.glbBinCurrPop[key])

   # first access for this bin
   for key in keyCurrEpochDiff:
      assert key not in g.glbBinOldPop
      g.glbBinOldPop[key] = [g.glbBinCurrPop[key]]

   # no access for this bin in last epoch
   for key in keyOldEpochsDiff:
      if len(g.glbBinOldPop[key]) == g.numOldEpoch:
         del g.glbBinOldPop[key][0]
      g.glbBinOldPop[key].append(0.0)



















def PopPredNextEpoch():

   #print '###########PopPredNextEpoch()##########'
   #print '===g.glbPolicy=',g.glbPolicy
   """
   Predict bin(s) should be cached in the next epoch based on predicted popularity.
   //bin popularity = access num in last epoch * reaccess probability in an epoch granularity.
   bin popularity = access number in the last epoch.
   """
   ##########################################################################################################################
   ##########################################################################################################################
   ##########################################################################################################################
   ##########################################################################################################################
   if g.glbPolicy == 0:
      #print '######## p=0 ########'
      if len(g.glbBinCurrPop) < g.NUM_BIN:
         keyNextEpoch = g.glbBinCurrPop.keys()
         keyInCache = g.cache.binInCache.keys()
         keyInst = set(keyInCache).intersection(keyNextEpoch)
         keyInCacheDiff = set(keyInCache).difference(keyInst)
         keyNextEpochDiff = set(keyNextEpoch).difference(keyInst)

         g.glbBinNextPop = copy.deepcopy(g.cache.binInCache)
         numEvict = len(keyNextEpochDiff) - (g.NUM_BIN - len(keyInCache))
         if 0 < numEvict < len(keyInCacheDiff):
            items = GetNSmallest(numEvict, keyInCacheDiff)
            # migrate out
            for key in items:
               del g.glbBinNextPop[key]
         else:
            assert numEvict <= 0
         # migrate in
         for key in keyNextEpochDiff:
            g.glbBinNextPop[key] = True
         assert len(g.glbBinNextPop) <= g.NUM_BIN
      elif len(g.glbBinCurrPop) == g.NUM_BIN:
         g.glbBinNextPop = dict.fromkeys(g.glbBinCurrPop.keys(), True)
      else:
         items = heapq.nlargest(g.NUM_BIN, g.glbBinCurrPop.iteritems(), key=operator.itemgetter(1))
         g.glbBinNextPop = dict.fromkeys(map(lambda i: i[0], items), True)


   ##########################################################################################################################
   ##########################################################################################################################
   ##########################################################################################################################
   ##########################################################################################################################
   elif g.glbPolicy == 1:
      #print '######## p=1 ########'
      # get extraBin & evictBin dicts and update g.wl[i].prvQue
      extraBin = []
      evictBin = []
      for i in xrange(g.numWL):
         keyWL = g.wl[i].binCurrPop.keys()
         keyPrv = g.wl[i].prvQue.keys()
         keyInst = set(keyWL).intersection(set(keyPrv))
         keyWLDiff = set(keyWL).difference(keyInst) ### yang note: extraBin and evictBin no dup!!!
         keyPrvDiff = set(keyPrv).difference(keyInst)

         if len(keyWL) < g.wl[i].numPrvBin:
            numEvict = len(keyWLDiff) - (g.wl[i].numPrvBin - len(g.wl[i].prvQue))
           #numEvict = new//need - (SIZE-prvQue)//remaining = prvQue should evict
           #or       = new + prvQue//already - totalSize
            assert numEvict < len(keyPrvDiff)
            if numEvict > 0:
               items = GetNSmallest(numEvict, keyPrvDiff)
               evictBin.extend(items)
               for key in items:
                  del g.wl[i].prvQue[key]
            for key in keyWLDiff:
               g.wl[i].prvQue[key] = True
            assert len(g.wl[i].prvQue) <= g.wl[i].numPrvBin
         elif len(keyWL) == g.wl[i].numPrvBin:
            evictBin.extend(keyPrvDiff)
            g.wl[i].prvQue = dict.fromkeys(keyWL, True)
         else: # len(keyWL) > g.wl[i].numPrvBin:
            evictBin.extend(keyPrvDiff)
            items = [[key, g.wl[i].binCurrPop[key]] for key in g.wl[i].binCurrPop]
            items.sort(key=operator.itemgetter(1))
            items = [key[0] for key in items]
            g.wl[i].prvQue = dict.fromkeys(items[-1*g.wl[i].numPrvBin:], True)
            extraBin.extend(items[:-1*g.wl[i].numPrvBin])

      # update g.pubQue
      #############################################################
      # case 1
      if len(extraBin) > g.NUM_PUBLIC_BIN:
#         items = [[key, g.glbBinCurrPop[key]] for key in extraBin]
#         items.sort(key=operator.itemgetter(1))
#         items = items[-1*g.NUM_PUBLIC_BIN:]
#         items = [key[0] for key in items]
         items = GetNLargest(g.NUM_PUBLIC_BIN, extraBin)
         g.pubQue = dict.fromkeys(items, True)
      elif len(extraBin) == g.NUM_PUBLIC_BIN:
         g.pubQue = dict.fromkeys(extraBin, True)
         #extraBin and evictBin no dup!!!
      #############################################################      
      # case 2
      elif len(extraBin) + len(evictBin) > g.NUM_PUBLIC_BIN:
         numAdmin = g.NUM_PUBLIC_BIN - len(extraBin)
         items = GetNLargest(numAdmin, evictBin)
         items.extend(extraBin)
         g.pubQue = dict.fromkeys(items, True)
      elif len(extraBin) + len(evictBin) == g.NUM_PUBLIC_BIN:
         evictBin.extend(extraBin)
         g.pubQue = dict.fromkeys(evictBin, True)
      #############################################################
      # case 3
      elif 0 < len(extraBin) + len(evictBin) < g.NUM_PUBLIC_BIN:
         keyRect = g.pubQue.keys()
         keyWL = g.glbBinCurrPop.keys() ### yang: note that this is another list contains last epoch's access glb bins' info
         # good idea, since we do not allow any existing bins in curPop to be in pr/pub que to affect assignment
         # for prvQue, each VM's del dup(prv,currPop) from prv
         # for pubQue, del dup(pub,currPopGlb) from pub 
         keyInst = set(keyRect).intersection(set(keyWL))
         for key in keyInst:
            del g.pubQue[key]
         numEvict = len(extraBin) + len(evictBin) - (g.NUM_PUBLIC_BIN - len(g.pubQue))
         if numEvict > 0:
            items = GetNSmallest(numEvict, g.pubQue.keys())
            for key in items:
               del g.pubQue[key]
         evictBin.extend(extraBin)
         g.pubQue.update(dict.fromkeys(evictBin, True))
         if numEvict > 0:
            assert len(g.pubQue) == g.NUM_PUBLIC_BIN
      else:
         assert len(extraBin) + len(evictBin) == 0
      #############################################################

      # update g.glbBinNextPop
      for i in xrange(g.numWL):
         g.glbBinNextPop.update(g.wl[i].prvQue)
         # yang 20150226
         g.glbBinNextPopPrv.update(g.wl[i].prvQue)#yang


      g.glbBinNextPop.update(g.pubQue)
      g.glbBinNextPopPub.update(g.pubQue) #yang
      assert len(g.glbBinNextPop) <= g.NUM_BIN





   ##########################################################################################################################
   ##########################################################################################################################
   ##########################################################################################################################
   ##########################################################################################################################
   elif g.glbPolicy == 2:
      ###g2
      #print '######## p=2 ########'
      #print '######## Before ########'
      g.prevPrvQue=g.prvQue
      g.prevPubQue=g.pubQue
           
      #print 'len(g.prevPrvQue)=',len(g.prevPrvQue)
      #print 'g.prvQue=',g.prvQue
     
      #print 'g.pubQue=',g.pubQue
      #print 'len(g.prevPubQue)=',len(g.prevPubQue)

      # update g.prvQue
      if len(g.glbBinCount) <= g.NUM_PRIVATE_BIN:
         g.prvQue = dict.fromkeys(g.glbBinCount.keys(), True)
      else: # len(g.glbBinCount) > g.NUM_PRIVATE_BIN 
         items = heapq.nlargest(g.NUM_PRIVATE_BIN, g.glbBinCount.iteritems(), key=operator.itemgetter(1))
         items = [key[0] for key in items]
         keyInst = set(items).intersection(set(g.prvQue))
         keyPrvDiff = []
         if len(g.prvQue) == g.NUM_PRIVATE_BIN:
            diffRatio = (g.NUM_PRIVATE_BIN - len(keyInst)) / float(g.NUM_PRIVATE_BIN)
            if diffRatio >= 0.2:
               keyPrvDiff = set(g.prvQue).difference(keyInst)
               g.prvQue = dict.fromkeys(items, True)
         else:
            keyPrvDiff = set(g.prvQue).difference(keyInst)
            g.prvQue = dict.fromkeys(items, True)

      # update g.pubQue
      if g.NUM_PRIVATE_BIN < len(g.glbBinCount) <= g.NUM_BIN:
         g.pubQue.clear()
         #for key in g.glbBinCount:
         #   if key not in g.prvQue:
         #      g.pubQue[key] = True

         i=0
         for key in g.glbBinCount:
            if key not in g.prvQue and i<g.NUM_PUBLIC_BIN: ### yang 20150108
               g.pubQue[key] = True ### top NUM_PUBLIC_BIN, added by YANG
               i=i+1



      elif len(g.glbBinCount) > g.NUM_BIN:
         # delete overlap key
         for key in g.prvQue:
            if key in g.pubQue:
               del g.pubQue[key]
            if key in g.glbBinCurrPop:
               del g.glbBinCurrPop[key]
         # get g.pubQue
         if len(g.glbBinCurrPop) > g.NUM_PUBLIC_BIN:
            items = heapq.nlargest(g.NUM_PUBLIC_BIN, g.glbBinCurrPop.iteritems(), key=operator.itemgetter(1))
            items = [key[0] for key in items]
            g.pubQue = dict.fromkeys(items, True)
         elif len(g.glbBinCurrPop) == g.NUM_PUBLIC_BIN:
            g.pubQue = dict.fromkeys(g.glbBinCurrPop.keys(), True)
         else:    # len(g.glbBinCurrPop) < g.NUM_PUBLIC_BIN:
            numAdmin = g.NUM_PUBLIC_BIN - len(g.glbBinCurrPop)
            keyPub = g.pubQue.keys() + list(keyPrvDiff)  # merge the evicted key of g.prvQue to g.pubQue
            keyInst = set(g.glbBinCurrPop).intersection(set(keyPub))
            keyPubDiff = set(keyPub).difference(keyInst)
            g.pubQue.clear()
            if len(keyPubDiff) <= numAdmin:
               g.pubQue = dict.fromkeys(keyPubDiff, True)
               g.pubQue.update(dict.fromkeys(g.glbBinCurrPop.keys(), True))
            else:
               items = GetNLargest(numAdmin, keyPubDiff)
               g.pubQue = dict.fromkeys(items, True)
               g.pubQue.update(dict.fromkeys(g.glbBinCurrPop.keys(), True))
               assert len(g.pubQue) + len(g.prvQue) == g.NUM_BIN
      #else: # len(g.glbBinCount) <= g.NUM_PRIVATE_BIN# ##############yang20150325 delete
      #   assert len(g.pubQue) == 0 and len(g.prvQue) == len(g.glbBinCount)

      # update g.glbBinNextPop
      g.glbBinNextPop.update(g.prvQue)
      g.glbBinNextPop.update(g.pubQue)
      g.glbBinNextPopPrv.update(g.prvQue)
      g.glbBinNextPopPub.update(g.pubQue)
      #if len(g.glbBinNextPop) <= g.NUM_BIN:
         #print '==##g.prvQue=', g.prvQue
         #print 'len(g.prvQue)=', len(g.prvQue) 
         #print 'g.pubQue=', g.pubQue
         #print 'len(g.pubQue)=', len(g.pubQue) 
      #assert len(g.glbBinNextPop) <= g.NUM_BIN
      




      ################################
      # update g.eviction history    #
      ################################
      #print '######## After ########'
      #print 'g.prvQue=',g.prvQue
      #print 'len(g.prvQue)=',len(g.prvQue)

      #print 'g.pubQue=',g.pubQue
      #print 'len(g.pubQue)=',len(g.pubQue)

      ### SSD ###
      g.entireCache=set(g.prvQue)
      g.entireCache=g.entireCache.union(set(g.pubQue))
      #print 'g.entireCache=',g.entireCache
      #print 'len(g.entireCache)=', len(g.entireCache)
      
      ### evictHistory ###
      g.prvEvict=set(g.prevPrvQue).difference(g.prvQue)
      g.curPrvEvictHistory=dict.fromkeys(g.prvEvict, True)
      #print 'g.curPrvEvictHistory=',g.curPrvEvictHistory
      #print 'len(g.curPrvEvictHistory)=',len(g.curPrvEvictHistory)

      g.pubEvict=set(g.prevPubQue).difference(g.pubQue)
      g.curPubEvictHistory=dict.fromkeys(g.pubEvict, True)
      #print 'g.curPubEvictHistory=',g.curPubEvictHistory
      #print 'len(g.curPubEvictHistory)=',len(g.curPubEvictHistory)

      ### overTimeEvictHistory ###
      for key in g.prvEvict:
         g.overtimePrvEvictHistory[key] = g.overtimePrvEvictHistory.get(key, 0) + 1
      #print 'overtimePrvEvictHistory=',g.overtimePrvEvictHistory
      #print 'len(g.overtimePrvEvictHistory)=',len(g.overtimePrvEvictHistory)

      for key in g.pubEvict:
         g.overtimePubEvictHistory[key] = g.overtimePubEvictHistory.get(key, 0) + 1
      #print 'overtimePubEvictHistory=',g.overtimePubEvictHistory
      #print 'len(g.overtimePubEvictHistory)=',len(g.overtimePubEvictHistory)


      ### evictionDupWithLastEpoch ###
      # curPrvEvictHistory, prevPrvEvictHistory
      g.prvDup = set(g.curPrvEvictHistory).intersection(set(g.prevPrvEvictHistory))
      #print 'g.prvDup=',g.prvDup
      #print 'len(g.prvDup)=',len(g.prvDup)

      g.pubDup = set(g.curPubEvictHistory).intersection(set(g.prevPubEvictHistory))
      #print 'g.pubDup=',g.pubDup
      #print 'len(g.pubDup)=',len(g.pubDup)

      ### evictDupWithHistory ###
      g.prvDupWithHistory = set(g.curPrvEvictHistory).intersection(set(g.overtimePrvEvictHistory))
      #print 'g.prvDupWithHistory=',g.prvDupWithHistory
      #print 'len(g.prvDupWithHistory)=',len(g.prvDupWithHistory)

      g.pubDupWithHistory = set(g.curPubEvictHistory).intersection(set(g.overtimePubEvictHistory))
      #print 'g.pubDupWithHistory=',g.pubDupWithHistory
      #print 'len(g.pubDupWithHistory)=',len(g.pubDupWithHistory)






      g.prvDupWithHistoryLog.write(str(len(g.prvDupWithHistory))+'\n')
      g.pubDupWithHistoryLog.write(str(len(g.pubDupWithHistory))+'\n')

      #g.prvDupWithLastEpochLog.write(str(len(g.prvDup))+'\n')
      #g.pubDupWithLastEpochLog.write(str(len(g.pubDup))+'\n')



      ################################################################################
      # clean up curEvict                                                            #
      ################################################################################
      g.prevPrvEvictHistory=g.curPrvEvictHistory
      g.curPrvEvictHistory.clear()
      g.prevPubEvictHistory=g.curPubEvictHistory
      g.curPubEvictHistory.clear()



   ##########################################################################################################################
   ##########################################################################################################################
   ##########################################################################################################################
   ##########################################################################################################################
   # others
   else: # other g.glbPolicy
      print 'ERROR: g.glbPolicy is wrong.'
      sys.exit(1)
   ##########################################################################################################################
   ##########################################################################################################################
   ##########################################################################################################################
   ##########################################################################################################################

def GetNSmallest(n, keyList):
   items = []
   for key in keyList:
      pop = 0.0
      for i in xrange(len(g.glbBinOldPop[key])):
         pop += g.epochWeight[i] * g.glbBinOldPop[key][-1*(i+1)]
      items.append([key, pop])
   items = heapq.nsmallest(n, items, key=operator.itemgetter(1))
   return map(lambda x: x[0], items)


def GetNLargest(n, keyList):
   items = []
   for key in keyList:
      pop = 0.0
      for i in xrange(len(g.glbBinOldPop[key])):
         pop += g.epochWeight[i] * g.glbBinOldPop[key][-1*(i+1)]
      items.append([key, pop])
   items = heapq.nlargest(n, items, key=operator.itemgetter(1))
   return map(lambda x: x[0], items)


class Cache:
   """
   Cache Simulator
   """
   def __init__(self):
      self.dirtyFlag = dict()    # hold dirty flag for each bin, format: {binID:(True/False)}
      self.binInCache = dict()
      self.binInPrvZone = dict() #yang 20150226
      self.binInPubZone = dict() #yang 20150226
      self.numHit = 0   # number of cache hit
      self.numHitInPrv = 0 #yang
      self.numHitInPub = 0 #yang
      self.numIO = 0    # number of I/O used for cache hit calculation after cache warm
      self.numRead = 0
      self.numWrite = 0

   #Set dirty flag
   def SetDirty(self, binID):
      self.dirtyFlag[binID] = True

   #Check dirty status
   def IsDirty(self, binID):
      return binID in self.dirtyFlag

   #Calculate the number of I/O eviction for dirty bin(1MB) in Write Back policy
   def WBEvictIOCost(self, binID):
      if g.writePolicy == 0 and self.IsDirty(binID):
         del self.dirtyFlag[binID]
         g.numEvict += g.NUM_IO_PER_BIN
         g.numSsdRead += g.NUM_IO_PER_BIN
         g.numMdWrite += g.NUM_IO_PER_BIN

   #Check if the data within bin is cached
   def CheckHit(self, binID):
      return binID in self.binInCache # true/false

   ######################### yang 20150302 #############
   #Check if the data within bin is cached in prvZone
   def CheckHitInPrv(self, binID):
      return binID in self.binInPrvZone # true/false

   #Check if the data within bin is cached in pubZone
   def CheckHitInPub(self, binID):
      return binID in self.binInPubZone # true/false
   #####################################################


   #Flush cached bins by migrating out/in
   def FlushBin(self):

      #print '#### flushBin() #####'
      keyInCache = self.binInCache.keys()
      keyNextEpoch = g.glbBinNextPop.keys()

      keyInst = set(keyInCache).intersection(keyNextEpoch)
      keyInCacheDiff = set(keyInCache).difference(keyInst)
      keyNextEpochDiff = set(keyNextEpoch).difference(keyInst)


      #print 'keyInCache=',keyInCache
      #print 'keyNextEpoch=',keyNextEpoch
      #print 'keyNextEpochDiff=',keyNextEpochDiff 
      #print 'len(keyInCacheDiff)=',len(keyInCacheDiff)

      if (g.glbPolicy == 0 or g.glbPolicy == 2 ) and len(keyNextEpoch) < g.NUM_BIN:
         assert len(keyInCacheDiff) == 0

      for key in keyInCacheDiff:
         self.WBEvictIOCost(key)
      for key in self.dirtyFlag:
         if key not in keyInst:
            print 'Error: test error.'
            sys.exit(1)
      g.numAdmin += len(keyNextEpochDiff) * g.NUM_IO_PER_BIN
      g.numMdRead += len(keyNextEpochDiff) * g.NUM_IO_PER_BIN
      g.numSsdWrite += len(keyNextEpochDiff) * g.NUM_IO_PER_BIN

      self.binInCache.clear()
      self.binInCache = copy.deepcopy(g.glbBinNextPop)
      ###################yang prvpubbin
      # yang 20150226
      self.binInPrvZone.clear()
      self.binInPrvZone = copy.deepcopy(g.glbBinNextPopPrv)
      self.binInPubZone.clear()
      self.binInPubZone = copy.deepcopy(g.glbBinNextPopPub)

def WindowsTickToUnixSeconds(windowsTicks):
   """
   Convert Windows filetime to Unix time.
   The windows epoch starts 1601-01-01T00:00:00Z.
   It's 11644473600 seconds before the UNIX/Linux
   epoch (1970-01-01T00:00:00Z). The Windows ticks
   are in 100 nanoseconds.
   """
   ticksPerSecond = 10000000
   epochDifference = 11644473600L
   return windowsTicks / ticksPerSecond - epochDifference


def GetTraceReference(inFile, lineNum):
   """
   Get specified line from input file.
   """
   line = linecache.getline(inFile, lineNum)
   if line != '':
      # Pick up reference from I/O trace line
      line = line.strip().split(',')
      ioTime = WindowsTickToUnixSeconds(long(line[0]))
      ioLBN = long(line[4]) / 512
      ioSize = long(line[5]) / 512
      ioRW = line[3]
      if ioRW == 'Write':
         ioRW = 'W'
      elif ioRW == 'Read':
         ioRW = 'R'
      else:
         print 'Error: wrong W/R format'
         sys.exit(1)
      return [ioTime, ioRW, ioLBN, ioSize]
   else:
      return [0, 0, 0, 0]


def PrintSummary():
   """
   Print results of program execution. This is called at the
   end of the program run to provide a summary of what settings
   were used and the resulting hit ratio.
   """

   print '|--------------------------------------------|'
   print '|    Input files(%d):' % g.numWL,
   for i in xrange(g.numWL):
      print g.wl[i].inFile,
   print ''
   print '|    Flash size: %dMB' % (g.FLASH_SIZE)
   print '|    Write Policy: %s' % (g.wrAbbr)
   print '|    Flash admin num: %d' % (g.numAdmin)
   print '|    Flash evict num: %d' % (g.numEvict)
   print '|    Bypass flash num: %d' % (g.numBypass)
   print '|    SSD read num: %d' % (g.numSsdRead)
   print '|    SSD write num: %d' % (g.numSsdWrite)
   print '|    MD read num: %d' % (g.numMdRead)
   print '|    MD write num: %d' % (g.numMdWrite)
   print '|    Cache hit ratio: %.4f%%' % (float(g.cache.numHit) / g.cache.numIO * 100)
   print '|--------------------------------------------|'

   if g.numWL == 1:
      outFile = open(os.path.join(g.dirPath, '%sSummary-%s-%dmin-%dMB-%s' % (g.outPrefix, g.dirName, g.REPLACE_EPOCH/60, g.FLASH_SIZE, g.wrAbbr)), 'a')
      outFile.write('Input file: %s\n' % g.wl[0].inFile)
      outFile.write('Flash size: %d(MB)\n' % (g.FLASH_SIZE))
      outFile.write('Write policy: %s\n' % (g.wrAbbr))
      outFile.write('Time length: %.4f(hour)\n' % (g.wl[0].timeLength))
      outFile.write('Number of I/Os: %d\n' % (g.cache.numIO))
      outFile.write('Number of Read: %d\n' % (g.cache.numRead))
      outFile.write('Number of Write: %d\n' % (g.cache.numWrite))
      outFile.write('Flash admin num: %d\n' % (g.numAdmin))
      outFile.write('Flash evict num: %d\n' % (g.numEvict))
      outFile.write('Bypass flash num: %d\n' % (g.numBypass))
      outFile.write('SSD read num: %d\n' % (g.numSsdRead))
      outFile.write('SSD write num: %d\n' % (g.numSsdWrite))
      outFile.write('MD read num: %d\n' % (g.numMdRead))
      outFile.write('MD write num: %d\n' % (g.numMdWrite))
      outFile.write('Cache hit ratio: %.4f%%\n' % (float(g.cache.numHit) / g.cache.numIO * 100))
      ###### yang 20150302 #################################################################################################
      outFile.write('HitRatioInPrvZone: %.4f%%\n' % (float(g.cache.numHitInPrv) / g.cache.numIO * 100))
      outFile.write('HitRatioInPubZone: %.4f%%\n' % (float(g.cache.numHitInPub) / g.cache.numIO * 100))
      outFile.write('Total IO Num: %d\n'          % (g.cache.numIO) )
      outFile.write('Hit Num: %d\n'               % (g.cache.numHitInPrv) )
      outFile.write('HitInPrvZone Num: %d\n'      % (g.cache.numHitInPrv) )
      outFile.write('HitInPubZone Num: %d\n'      % (g.cache.numHitInPub) )
      ######################################################################################################################
      outFile.write('\n')
      outFile.close()
   else:
      outFile = open(os.path.join(g.dirPath, '%sSummary-%dfile-%dmin-%dMB-%s-glb%d' % (g.outPrefix, g.numWL, g.REPLACE_EPOCH/60, g.FLASH_SIZE, g.wrAbbr, g.glbPolicy)), 'a')
      outFile.write('Flash size: %d(MB)\n' % g.FLASH_SIZE)
      outFile.write('Write policy: %s\n' % (g.wrAbbr))
      outFile.write('Number of I/Os: %d\n' % g.cache.numIO)
      outFile.write('Number of Read: %d\n' % g.cache.numRead)
      outFile.write('Number of Write: %d\n' % g.cache.numWrite)
      outFile.write('Flash admin num: %d\n' % (g.numAdmin))
      outFile.write('Flash evict num: %d\n' % (g.numEvict))
      outFile.write('Bypass flash num: %d\n' % (g.numBypass))
      outFile.write('SSD read num: %d\n' % (g.numSsdRead))
      outFile.write('SSD write num: %d\n' % (g.numSsdWrite))
      outFile.write('MD read num: %d\n' % (g.numMdRead))
      outFile.write('MD write num: %d\n' % (g.numMdWrite))
      outFile.write('Cache hit ratio: %.4f%%\n' % (float(g.cache.numHit) / g.cache.numIO * 100))
      outFile.write('Input files(%d):\n' % (g.numWL))
      for i in xrange(g.numWL):
         outFile.write('%s:\t%d\t%d\t%d\t%.4f%%\n' % (g.wl[i].inFile, g.wl[i].numIOFlash, g.wl[i].numReadFlash, g.wl[i].numWriteFlash, (float(g.wl[i].numHit)/g.wl[i].numIOFlash*100)))
      ###### yang 20150302 #################################################################################################
      outFile.write('HitRatioInPrvZone: %.4f%%\n' % (float(g.cache.numHitInPrv) / g.cache.numIO * 100))
      outFile.write('HitRatioInPubZone: %.4f%%\n' % (float(g.cache.numHitInPub) / g.cache.numIO * 100))
      outFile.write('Total IO Num: %d\n'          % (g.cache.numIO) )
      outFile.write('Hit Num: %d\n'               % (g.cache.numHitInPrv) )
      outFile.write('HitInPrvZone Num: %d\n'      % (g.cache.numHitInPrv) )
      outFile.write('HitInPubZone Num: %d\n'      % (g.cache.numHitInPub) )
      ######################################################################################################################
      outFile.write('\n')
      outFile.close()


if __name__ == "__main__":
   main()
