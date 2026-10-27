module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data3
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data4
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data5

#bm_mul CFSG.KC.BM.Seven c_hi h [hi] I []
#bm_bool CFSG.KC.BM.Seven wf_hi (CFSG.KC.BM.wfMat hi)
#bm_mul CFSG.KC.BM.Seven c_t1 hi [z h] t1 []
#bm_bool CFSG.KC.BM.Seven wf_t1 (CFSG.KC.BM.wfMat t1)
#bm_mul CFSG.KC.BM.Seven c_y2 y [y] y2 []
#bm_bool CFSG.KC.BM.Seven wf_y2 (CFSG.KC.BM.wfMat y2)
#bm_mul CFSG.KC.BM.Seven c_y3 y [y2] y3 []
#bm_bool CFSG.KC.BM.Seven wf_y3 (CFSG.KC.BM.wfMat y3)
#bm_mul CFSG.KC.BM.Seven c_t2 y3 [t1 y2] t2 []
#bm_bool CFSG.KC.BM.Seven wf_t2 (CFSG.KC.BM.wfMat t2)
