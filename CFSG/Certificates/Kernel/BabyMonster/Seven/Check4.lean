module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data3

#bm_mul CFSG.KC.BM.Seven c_x r32 [r34] x []
#bm_bool CFSG.KC.BM.Seven wf_x (CFSG.KC.BM.wfMat x)
#bm_mul CFSG.KC.BM.Seven c_y r33 [x] y []
#bm_bool CFSG.KC.BM.Seven wf_y (CFSG.KC.BM.wfMat y)
