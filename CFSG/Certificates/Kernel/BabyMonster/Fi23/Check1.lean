module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data0
public import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data1
public import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data2
public import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data3
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data0

#bm_mul CFSG.KC.BM.Fi23 slp14 r13 [r13] r14 []
#bm_mul CFSG.KC.BM.Fi23 slp15 CFSG.KC.BM.Five.f1 [r14] r15 []
#bm_mul CFSG.KC.BM.Fi23 slp18 r15 [V] r6 [r15]
#bm_mul CFSG.KC.BM.Fi23 slp20 CFSG.KC.BM.Five.f0 [CFSG.KC.BM.Five.f2] r20 []
#bm_mul CFSG.KC.BM.Fi23 slp21 CFSG.KC.BM.Five.f2 [r20] r21 []
#bm_mul CFSG.KC.BM.Fi23 slp22 r21 [r21] r22 []
#bm_mul CFSG.KC.BM.Fi23 slp25 r22 [U] r11 [r22]
#bm_mul CFSG.KC.BM.Fi23 cg0 V [U] g0 []
#bm_mul CFSG.KC.BM.Fi23 cg1 g0 [V] g1 []
#bm_mul CFSG.KC.BM.Fi23 cg2 g0 [g0] g2 []
