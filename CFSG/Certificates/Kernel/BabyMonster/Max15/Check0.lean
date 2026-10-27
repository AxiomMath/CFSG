module

import CFSG.Certificates.Kernel.BabyMonster.Load
import CFSG.Certificates.Kernel.BabyMonster.LoadFour
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Data0
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0

#bm_mul4 CFSG.KC.BM.Max15 c_r32 CFSG.KC.BM.Seeds.A1 [CFSG.KC.BM.Seeds.A2] r32 []
#bm_mul4 CFSG.KC.BM.Max15 c_r36 r32 [r32] r36 []
#bm_mul4 CFSG.KC.BM.Max15 c_r37 CFSG.KC.BM.Seeds.A2 [r36] r37 []
#bm_mul4 CFSG.KC.BM.Max15 c_r41 r32 [r37] r41 []
#bm_mul4 CFSG.KC.BM.Max15 c_r45 r36 [r41] r45 []
#bm_mul4 CFSG.KC.BM.Max15 c_g2 r36 [r45 r37 r41 CFSG.KC.BM.Seeds.A2] g2 []
#bm_mul4 CFSG.KC.BM.Max15 c_r16 g2 [g2] r16 []
