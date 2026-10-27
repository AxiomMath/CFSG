module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data0
public import CFSG.Certificates.Kernel.BabyMonster.SevenGen.Data0
public import CFSG.Certificates.Kernel.BabyMonster.SevenGen.Data1
public import CFSG.Certificates.Kernel.BabyMonster.SevenGen.Data2

#bm_mul CFSG.KC.BM.SevenGen c_abi CFSG.KC.BM.Seven.r0 [abi] I []
#bm_bool CFSG.KC.BM.SevenGen wf_abi (CFSG.KC.BM.wfMat abi)
#bm_mul CFSG.KC.BM.SevenGen c_r53 x9 [abi x9 CFSG.KC.BM.Seven.r0] r53 []
#bm_bool CFSG.KC.BM.SevenGen wf_r53 (CFSG.KC.BM.wfMat r53)
#bm_mul CFSG.KC.BM.SevenGen c_r80 r53 [r53] r80 []
#bm_bool CFSG.KC.BM.SevenGen wf_r80 (CFSG.KC.BM.wfMat r80)
#bm_mul CFSG.KC.BM.SevenGen c_r81 r80 [r80] r81 []
#bm_bool CFSG.KC.BM.SevenGen wf_r81 (CFSG.KC.BM.wfMat r81)
#bm_mul CFSG.KC.BM.SevenGen c_r54 r53 [r81] r54 []
#bm_bool CFSG.KC.BM.SevenGen wf_r54 (CFSG.KC.BM.wfMat r54)
