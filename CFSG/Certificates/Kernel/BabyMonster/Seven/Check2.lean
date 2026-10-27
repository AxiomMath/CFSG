module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data0
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data1
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data2
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0

#bm_mul CFSG.KC.BM.Seven c_al m2 [r30] al []
#bm_bool CFSG.KC.BM.Seven wf_al (CFSG.KC.BM.wfMat al)
#bm_mul CFSG.KC.BM.Seven c_r4 CFSG.KC.BM.Seeds.A1 [al] r4 []
#bm_bool CFSG.KC.BM.Seven wf_r4 (CFSG.KC.BM.wfMat r4)
#bm_mul CFSG.KC.BM.Seven c_r31 r4 [r4] r31 []
#bm_bool CFSG.KC.BM.Seven wf_r31 (CFSG.KC.BM.wfMat r31)
#bm_mul CFSG.KC.BM.Seven c_m1 r4 [r31] m1 []
#bm_bool CFSG.KC.BM.Seven wf_m1 (CFSG.KC.BM.wfMat m1)
#bm_mul CFSG.KC.BM.Seven c_m2i m2 [m2i] I []
#bm_bool CFSG.KC.BM.Seven wf_m2i (CFSG.KC.BM.wfMat m2i)
#bm_mul CFSG.KC.BM.Seven c_r42 m1 [m2] r42 []
#bm_bool CFSG.KC.BM.Seven wf_r42 (CFSG.KC.BM.wfMat r42)
#bm_mul CFSG.KC.BM.Seven c_r46 r42 [r26] r46 []
#bm_bool CFSG.KC.BM.Seven wf_r46 (CFSG.KC.BM.wfMat r46)
