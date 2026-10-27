module

import CFSG.Certificates.Kernel.BabyMonster.Load
import CFSG.Certificates.Kernel.BabyMonster.LoadFour
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data1
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data3
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data4
public import CFSG.Certificates.Kernel.BabyMonster.B7J.Data0

#bm_mul4 CFSG.KC.BM.B7J c_f u [CFSG.KC.BM.Seven.y u CFSG.KC.BM.Seven.y4] f []
#bm_mul4 CFSG.KC.BM.B7J c_f2 f [f] f2 []
#bm_mul4 CFSG.KC.BM.B7J rel_f f2 [f] I []
#bm_mul4 CFSG.KC.BM.B7J c_g u [CFSG.KC.BM.Seven.y] g []
#bm_mul4 CFSG.KC.BM.B7J c_g2 g [g] g2 []
#bm_mul4 CFSG.KC.BM.B7J c_g4 g2 [g2] g4 []
#bm_mul4 CFSG.KC.BM.B7J rel_g g4 [g2 g] CFSG.KC.BM.Seven.al []
