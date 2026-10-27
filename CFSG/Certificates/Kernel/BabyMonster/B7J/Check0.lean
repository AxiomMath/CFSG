module

import CFSG.Certificates.Kernel.BabyMonster.Load
import CFSG.Certificates.Kernel.BabyMonster.LoadFour
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data1
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data3
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data4
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data5
public import CFSG.Certificates.Kernel.BabyMonster.SevenElem.Data0
public import CFSG.Certificates.Kernel.BabyMonster.B7J.Data0

#bm_mul4 CFSG.KC.BM.B7J c_ey CFSG.KC.BM.Seven.e3 [CFSG.KC.BM.Seven.y] ey []
#bm_mul4 CFSG.KC.BM.B7J c_ey2 ey [ey] ey2 []
#bm_mul4 CFSG.KC.BM.B7J c_ey4 ey2 [ey2] ey4 []
#bm_mul4 CFSG.KC.BM.B7J ord_ey ey4 [ey2 ey] CFSG.KC.BM.Seven.al []
#bm_mul4 CFSG.KC.BM.B7J c_b CFSG.KC.BM.Seven.y4 [CFSG.KC.BM.Seven.e3 CFSG.KC.BM.Seven.y4 CFSG.KC.BM.SevenElem.e2] b []
#bm_mul4 CFSG.KC.BM.B7J c_u b [b] u []
#bm_mul4 CFSG.KC.BM.B7J inv_u u [u] I []
