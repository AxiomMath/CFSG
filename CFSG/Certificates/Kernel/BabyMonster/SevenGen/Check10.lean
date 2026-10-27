module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data3
public import CFSG.Certificates.Kernel.BabyMonster.SevenGen.Data5

#bm_mul CFSG.KC.BM.SevenGen c_r91 r90 [r90] r91 []
#bm_bool CFSG.KC.BM.SevenGen wf_r91 (CFSG.KC.BM.wfMat r91)
#bm_mul CFSG.KC.BM.SevenGen c_r92 r90 [r91] r92 []
#bm_bool CFSG.KC.BM.SevenGen wf_r92 (CFSG.KC.BM.wfMat r92)
#bm_mul CFSG.KC.BM.SevenGen c_bp bpw [r92] bp []
#bm_bool CFSG.KC.BM.SevenGen wf_bp (CFSG.KC.BM.wfMat bp)
#bm_mul CFSG.KC.BM.SevenGen c_f ci [CFSG.KC.BM.Seven.x c] f []
#bm_bool CFSG.KC.BM.SevenGen wf_f (CFSG.KC.BM.wfMat f)
