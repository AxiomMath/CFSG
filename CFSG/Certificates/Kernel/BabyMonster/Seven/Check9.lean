module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data3
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data4
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data5

#bm_mul CFSG.KC.BM.Seven c_y4 y2 [y2] y4 []
#bm_bool CFSG.KC.BM.Seven wf_y4 (CFSG.KC.BM.wfMat y4)
#bm_mul CFSG.KC.BM.Seven c_r43 t1 [y] r43 []
#bm_bool CFSG.KC.BM.Seven wf_r43 (CFSG.KC.BM.wfMat r43)
#bm_mul CFSG.KC.BM.Seven c_r40 t1 [y4] r40 []
#bm_bool CFSG.KC.BM.Seven wf_r40 (CFSG.KC.BM.wfMat r40)
#bm_mul CFSG.KC.BM.Seven c_r44 r40 [r40] r44 []
#bm_bool CFSG.KC.BM.Seven wf_r44 (CFSG.KC.BM.wfMat r44)
#bm_mul CFSG.KC.BM.Seven c_r47 r43 [r44] r47 []
#bm_bool CFSG.KC.BM.Seven wf_r47 (CFSG.KC.BM.wfMat r47)
