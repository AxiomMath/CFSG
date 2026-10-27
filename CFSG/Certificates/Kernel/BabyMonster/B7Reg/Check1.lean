module

import CFSG.Certificates.Kernel.BabyMonster.Load
import CFSG.Certificates.Kernel.BabyMonster.LoadFour
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data3
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data4
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data5
public import CFSG.Certificates.Kernel.BabyMonster.B7Reg.Data0
public import CFSG.Certificates.Kernel.BabyMonster.B7Reg.Data1

#bm_mul4 CFSG.KC.BM.B7Reg c_yb CFSG.KC.BM.Seven.r33 [CFSG.KC.BM.Seven.r32 CFSG.KC.BM.Seven.r34] yb []
#bm_mul4 CFSG.KC.BM.B7Reg inv_yb CFSG.KC.BM.Seven.y4 [yb] I []
#bm_mul4 CFSG.KC.BM.B7Reg c_p CFSG.KC.BM.Seven.hi [CFSG.KC.BM.Seven.z CFSG.KC.BM.Seven.h yb] p []
#bm_mul4 CFSG.KC.BM.B7Reg c_q CFSG.KC.BM.Seven.hi [CFSG.KC.BM.Seven.z CFSG.KC.BM.Seven.h CFSG.KC.BM.Seven.y4] q []
#bm_mul4 CFSG.KC.BM.B7Reg c_q2 q [q] q2 []
#bm_mul4 CFSG.KC.BM.B7Reg c_q4 q2 [q2] q4 []
#bm_mul4 CFSG.KC.BM.B7Reg c_t2b CFSG.KC.BM.Seven.y4 [CFSG.KC.BM.Seven.y4 p yb] t2b []
