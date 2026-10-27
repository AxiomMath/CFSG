module

import CFSG.Certificates.Kernel.BabyMonster.LoadFour
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
public import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data0
public import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data1
public import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data2
public import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data3
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0

#bm_mul4 CFSG.KC.BM.FiveA cp11 p10 [v8] p11 []
#bm_mul4 CFSG.KC.BM.FiveA cv12 p6 [CFSG.KC.BM.Seeds.A1 CFSG.KC.BM.Seeds.A2 CFSG.KC.BM.Seeds.A1 p6 CFSG.KC.BM.Seeds.A1] v12 []
#bm_mul4 CFSG.KC.BM.FiveA cv13 CFSG.KC.BM.Seeds.A1 [CFSG.KC.BM.Seeds.A2 CFSG.KC.BM.Seeds.A1 p6 CFSG.KC.BM.Seeds.A1 CFSG.KC.BM.Seeds.A2] v13 []
#bm_mul4 CFSG.KC.BM.FiveA cv14 p11 [v12 p11 v13] v14 []
#bm_mul4 CFSG.KC.BM.FiveA cp15 v14 [v14] p15 []
#bm_mul4 CFSG.KC.BM.FiveA cp16 p15 [p15] p16 []
#bm_mul4 CFSG.KC.BM.FiveA cp17 p16 [p16] p17 []
#bm_mul4 CFSG.KC.BM.FiveA cp18 p17 [v14] p18 []
#bm_mul4 CFSG.KC.BM.FiveA cp19 p18 [p18] p19 []
#bm_mul4 CFSG.KC.BM.FiveA cp20 p19 [v14] p20 []
#bm_mul4 CFSG.KC.BM.FiveA cv21 v13 [p20] v21 []
#bm_mul4 CFSG.KC.BM.FiveA cp22 v21 [v21] p22 []
#bm_mul4 CFSG.KC.BM.FiveA cp23 p22 [v21] p23 []
#bm_mul4 CFSG.KC.BM.FiveA cp24 p23 [p23] p24 []
