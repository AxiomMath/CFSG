module

import CFSG.Certificates.Kernel.BabyMonster.Load
import CFSG.Certificates.Kernel.BabyMonster.LoadFour
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
public import CFSG.Certificates.Kernel.BabyMonster.B11.Data10
public import CFSG.Certificates.Kernel.BabyMonster.B11.Data11

#bm_mul4 CFSG.KC.BM.B11 cm02 x2 [x0] p02 []
#bm_mul4 CFSG.KC.BM.B11 cm03 x0 [x3] x3 [x0]
#bm_mul4 CFSG.KC.BM.B11 cm13 x1 [x3] x3 [x1]
#bm_bool CFSG.KC.BM.B11 ne_p02 (CFSG.KC.BM.notB (CFSG.KC.BM.isId p02))
