module

import CFSG.Certificates.Kernel.BabyMonster.Load
import CFSG.Certificates.Kernel.BabyMonster.LoadFour
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data1
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data4
public import CFSG.Certificates.Kernel.BabyMonster.B7J.Data0

#bm_mul4 CFSG.KC.BM.B7J c_c1 u [CFSG.KC.BM.Seven.y3] c1 []
#bm_mul4 CFSG.KC.BM.B7J c_c2 c1 [c1] c2 []
#bm_mul4 CFSG.KC.BM.B7J c_c4 c2 [c2] c4 []
#bm_mul4 CFSG.KC.BM.B7J rel_c c4 [c2 c1] CFSG.KC.BM.Seven.al []
#bm_mul4 CFSG.KC.BM.B7J c_d u [CFSG.KC.BM.Seven.y3 u CFSG.KC.BM.Seven.y2] d []
#bm_mul4 CFSG.KC.BM.B7J c_d2 d [d] d2 []
#bm_mul4 CFSG.KC.BM.B7J rel_d d2 [d2] I []
