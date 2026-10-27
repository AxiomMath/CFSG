module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data0
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data1
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data2
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data3

#bm_mul CFSG.KC.BM.Seven c_r41 m1 [m2i] r41 []
#bm_bool CFSG.KC.BM.Seven wf_r41 (CFSG.KC.BM.wfMat r41)
#bm_mul CFSG.KC.BM.Seven c_r45 r41 [m2i] r45 []
#bm_bool CFSG.KC.BM.Seven wf_r45 (CFSG.KC.BM.wfMat r45)
#bm_mul CFSG.KC.BM.Seven c_g r46 [m2 r45] g []
#bm_bool CFSG.KC.BM.Seven wf_g (CFSG.KC.BM.wfMat g)
#bm_mul CFSG.KC.BM.Seven c_r32 g [g] r32 []
#bm_bool CFSG.KC.BM.Seven wf_r32 (CFSG.KC.BM.wfMat r32)
#bm_mul CFSG.KC.BM.Seven c_r33 r32 [r32] r33 []
#bm_bool CFSG.KC.BM.Seven wf_r33 (CFSG.KC.BM.wfMat r33)
#bm_mul CFSG.KC.BM.Seven c_r34 r33 [r33] r34 []
#bm_bool CFSG.KC.BM.Seven wf_r34 (CFSG.KC.BM.wfMat r34)
