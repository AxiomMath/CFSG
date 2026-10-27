module

import CFSG.Certificates.Kernel.BabyMonster.LoadFour
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data14
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data19
public import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data0
public import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data1
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0

#bm_mul4 CFSG.KC.BM.FiveA ca1 CFSG.KC.BM.Five.f85 [CFSG.KC.BM.Five.f86_sq2 CFSG.KC.BM.Five.f85_sq2] a1 []
#bm_mul4 CFSG.KC.BM.FiveA cp2 CFSG.KC.BM.Five.f86_sq1 [CFSG.KC.BM.Five.f86_sq2] p2 []
#bm_mul4 CFSG.KC.BM.FiveA ca3 CFSG.KC.BM.Five.oh_p [a1 p2 a1 CFSG.KC.BM.Five.H3 a1 CFSG.KC.BM.Five.f86_sq2] a3 []
#bm_mul4 CFSG.KC.BM.FiveA cb4 CFSG.KC.BM.Five.Q2 [CFSG.KC.BM.Five.Q3] b4 []
#bm_mul4 CFSG.KC.BM.FiveA cb5 CFSG.KC.BM.Five.f86_sq2 [b4] b5 []
#bm_mul4 CFSG.KC.BM.FiveA cp6 CFSG.KC.BM.Seeds.A2 [CFSG.KC.BM.Seeds.A2] p6 []
#bm_mul4 CFSG.KC.BM.FiveA cp7 CFSG.KC.BM.Five.f86 [CFSG.KC.BM.Five.f86_sq2] p7 []
#bm_mul4 CFSG.KC.BM.FiveA cv8 p2 [CFSG.KC.BM.Five.f85 CFSG.KC.BM.Five.oh_p CFSG.KC.BM.Five.f85 CFSG.KC.BM.Five.f86_sq1 CFSG.KC.BM.Five.f85_sq2 CFSG.KC.BM.Five.f86 CFSG.KC.BM.Five.f85 p2 CFSG.KC.BM.Five.Q4_sq2] v8 []
#bm_mul4 CFSG.KC.BM.FiveA cp9 v8 [v8] p9 []
#bm_mul4 CFSG.KC.BM.FiveA cp10 p9 [p9] p10 []
