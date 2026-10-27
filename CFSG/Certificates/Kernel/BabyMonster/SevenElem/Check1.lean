module

import CFSG.Certificates.Kernel.BabyMonster.Load
import CFSG.Certificates.Kernel.BabyMonster.LoadFour
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data1
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data3
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data5
public import CFSG.Certificates.Kernel.BabyMonster.SevenElem.Data0

#bm_mul4 CFSG.KC.BM.SevenElem cm_t2t1 CFSG.KC.BM.Seven.t2 [CFSG.KC.BM.Seven.t1] t12 []
#bm_mul4 CFSG.KC.BM.SevenElem cm_et1 CFSG.KC.BM.Seven.e3 [CFSG.KC.BM.Seven.t1] tw []
#bm_mul4 CFSG.KC.BM.SevenElem cm_xt1 CFSG.KC.BM.Seven.x [CFSG.KC.BM.Seven.t1] t1x []
#bm_mul4 CFSG.KC.BM.SevenElem cm_alm1 CFSG.KC.BM.Seven.al [CFSG.KC.BM.Seven.m1] CFSG.KC.BM.Seven.m1 [CFSG.KC.BM.Seven.al]
#bm_bool CFSG.KC.BM.SevenElem ne_e (CFSG.KC.BM.notB (CFSG.KC.BM.isId CFSG.KC.BM.Seven.e3))
#bm_bool CFSG.KC.BM.SevenElem ne_y (CFSG.KC.BM.notB (CFSG.KC.BM.isId CFSG.KC.BM.Seven.y))
#bm_bool CFSG.KC.BM.SevenElem ne_cc (CFSG.KC.BM.notB (CFSG.KC.BM.isId cc))
#bm_bool CFSG.KC.BM.SevenElem ne_cc_al (CFSG.KC.BM.notB (CFSG.KC.BM.eqMat cc CFSG.KC.BM.Seven.al))
#bm_bool CFSG.KC.BM.SevenElem ne_t1_al (CFSG.KC.BM.notB (CFSG.KC.BM.eqMat CFSG.KC.BM.Seven.t1 CFSG.KC.BM.Seven.al))
#bm_bool CFSG.KC.BM.SevenElem ne_t1_t2 (CFSG.KC.BM.notB (CFSG.KC.BM.eqMat CFSG.KC.BM.Seven.t1 CFSG.KC.BM.Seven.t2))
