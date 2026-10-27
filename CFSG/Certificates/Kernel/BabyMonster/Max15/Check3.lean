module

import CFSG.Certificates.Kernel.BabyMonster.Load
import CFSG.Certificates.Kernel.BabyMonster.LoadFour
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Data0
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Data1
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Data2
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Data3
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0

#bm_mul4 CFSG.KC.BM.Max15 c_r23 r22 [r1] r23 []
#bm_mul4 CFSG.KC.BM.Max15 c_r26 r23 [r23] r26 []
#bm_mul4 CFSG.KC.BM.Max15 c_r24 r20 [r22] r24 []
#bm_mul4 CFSG.KC.BM.Max15 c_r27 CFSG.KC.BM.Seeds.A1 [r24] r27 []
#bm_mul4 CFSG.KC.BM.Max15 c_r28 r26 [r27] r28 []
#bm_mul4 CFSG.KC.BM.Max15 c_r29 r6 [r28] r29 []
#bm_mul4 CFSG.KC.BM.Max15 c_r7 r29 [r22] r7 []
#bm_mul4 CFSG.KC.BM.Max15 c_r8 r7 [r8] I []
#bm_bool CFSG.KC.BM.Max15 wf_r8 (CFSG.KC.BM.wfMat r8)
#bm_mul4 CFSG.KC.BM.Max15 c_r30 r1 [r29] r30 []
#bm_mul4 CFSG.KC.BM.Max15 c_r31 r8 [r30] r31 []
