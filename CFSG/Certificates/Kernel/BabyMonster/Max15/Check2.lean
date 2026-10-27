module

import CFSG.Certificates.Kernel.BabyMonster.Load
import CFSG.Certificates.Kernel.BabyMonster.LoadFour
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Data0
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Data1
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Data2
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0

#bm_mul4 CFSG.KC.BM.Max15 c_r15 r14 [r14] r15 []
#bm_mul4 CFSG.KC.BM.Max15 c_r3 r2 [r15] r3 []
#bm_mul4 CFSG.KC.BM.Max15 c_r4 r1 [r4] I []
#bm_bool CFSG.KC.BM.Max15 wf_r4 (CFSG.KC.BM.wfMat r4)
#bm_mul4 CFSG.KC.BM.Max15 c_r21 CFSG.KC.BM.Seeds.A1 [r3] r21 []
#bm_mul4 CFSG.KC.BM.Max15 c_r20 CFSG.KC.BM.Seeds.A1 [r1] r20 []
#bm_mul4 CFSG.KC.BM.Max15 c_r22 r21 [r20] r22 []
#bm_mul4 CFSG.KC.BM.Max15 c_r5 r4 [r22 r22 r22] r5 []
#bm_mul4 CFSG.KC.BM.Max15 c_r6 r5 [r6] I []
#bm_bool CFSG.KC.BM.Max15 wf_r6 (CFSG.KC.BM.wfMat r6)
