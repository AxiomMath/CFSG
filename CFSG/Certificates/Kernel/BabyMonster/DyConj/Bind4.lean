module

import CFSG.Certificates.Kernel.BabyMonster.Load
import CFSG.Certificates.Kernel.BabyMonster.LoadRange
public import CFSG.Certificates.Kernel.BabyMonster.Native.DyConj
public import CFSG.Certificates.Kernel.BabyMonster.DyConj.Data2
public import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Data7

set_option maxRecDepth 100000

#bm_range CFSG.KC.BM.DyConj b23_ 0 69 (CFSG.KC.BM.cjBlk CFSG.KC.BM.FixedLine.C23.rows S23)
#bm_bool CFSG.KC.BM.DyConj wf23 (CFSG.KC.BM.wfMatn 4371 S23)
