module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data0
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data1
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data5
public import CFSG.Certificates.Kernel.BabyMonster.SevenGen.Data0
public import CFSG.Certificates.Kernel.BabyMonster.SevenGen.Data2
public import CFSG.Certificates.Kernel.BabyMonster.SevenGen.Data3
public import CFSG.Certificates.Kernel.BabyMonster.SevenGen.Data4
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0

#bm_mul CFSG.KC.BM.SevenGen c_n2 CFSG.KC.BM.Seven.r0 [r54] n2 []
#bm_bool CFSG.KC.BM.SevenGen wf_n2 (CFSG.KC.BM.wfMat n2)
#bm_mul CFSG.KC.BM.SevenGen c_n2i n2 [n2i] I []
#bm_bool CFSG.KC.BM.SevenGen wf_n2i (CFSG.KC.BM.wfMat n2i)
#bm_mul CFSG.KC.BM.SevenGen c_alt1 CFSG.KC.BM.Seven.al [CFSG.KC.BM.Seven.t1] alt1 []
#bm_bool CFSG.KC.BM.SevenGen wf_alt1 (CFSG.KC.BM.wfMat alt1)
#bm_mul CFSG.KC.BM.SevenGen c_r66 r50 [CFSG.KC.BM.Seeds.A1 alt1] r66 []
#bm_bool CFSG.KC.BM.SevenGen wf_r66 (CFSG.KC.BM.wfMat r66)
#bm_mul CFSG.KC.BM.SevenGen c_r82 r66 [r66] r82 []
#bm_bool CFSG.KC.BM.SevenGen wf_r82 (CFSG.KC.BM.wfMat r82)
#bm_mul CFSG.KC.BM.SevenGen c_r83 r82 [r82] r83 []
#bm_bool CFSG.KC.BM.SevenGen wf_r83 (CFSG.KC.BM.wfMat r83)
