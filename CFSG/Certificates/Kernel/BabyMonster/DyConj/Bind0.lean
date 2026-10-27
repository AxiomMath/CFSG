module

import CFSG.Certificates.Kernel.BabyMonster.Load
import CFSG.Certificates.Kernel.BabyMonster.LoadRange
public import CFSG.Certificates.Kernel.BabyMonster.Native.DyConj
public import CFSG.Certificates.Kernel.BabyMonster.DyConj.Data0
public import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Data1
public import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Data2

set_option maxRecDepth 100000

#bm_range CFSG.KC.BM.DyConj b1_ 0 69 (CFSG.KC.BM.cjBlk CFSG.KC.BM.FixedLine.C1.rows S1)
#bm_bool CFSG.KC.BM.DyConj wf1 (CFSG.KC.BM.wfMatn 4371 S1)
#bm_range CFSG.KC.BM.DyConj b2_ 0 69 (CFSG.KC.BM.cjBlk CFSG.KC.BM.FixedLine.C2.rows S2)
#bm_bool CFSG.KC.BM.DyConj wf2 (CFSG.KC.BM.wfMatn 4371 S2)
#bm_range CFSG.KC.BM.DyConj b3_ 0 69 (CFSG.KC.BM.cjBlk CFSG.KC.BM.FixedLine.C3.rows S3)
#bm_bool CFSG.KC.BM.DyConj wf3 (CFSG.KC.BM.wfMatn 4371 S3)
#bm_range CFSG.KC.BM.DyConj b4_ 0 69 (CFSG.KC.BM.cjBlk CFSG.KC.BM.FixedLine.C4.rows S4)
#bm_bool CFSG.KC.BM.DyConj wf4 (CFSG.KC.BM.wfMatn 4371 S4)
#bm_range CFSG.KC.BM.DyConj b5_ 0 69 (CFSG.KC.BM.cjBlk CFSG.KC.BM.FixedLine.C5.rows S5)
#bm_bool CFSG.KC.BM.DyConj wf5 (CFSG.KC.BM.wfMatn 4371 S5)
