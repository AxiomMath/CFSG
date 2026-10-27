module

import CFSG.Certificates.Kernel.BabyMonster.LoadFour
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data1
public import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data2
public import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data6
public import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data8
public import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data9
public import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data10
public import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data11
public import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data12
public import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data14
public import CFSG.Certificates.Kernel.BabyMonster.Fu.Data0
public import CFSG.Certificates.Kernel.BabyMonster.Fu.Data1
public import CFSG.Certificates.Kernel.BabyMonster.Fu.Data2
public import CFSG.Certificates.Kernel.BabyMonster.Fu.Data3
public import CFSG.Certificates.Kernel.BabyMonster.Fu.Data4
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Data0
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Data1

#bm_mul4 CFSG.KC.BM.Fu cVi CFSG.KC.BM.Fi23.V [CFSG.KC.BM.Fi23.V] Vi []
#bm_mul4 CFSG.KC.BM.Fu ccsq CFSG.KC.BM.Max2.r11 [CFSG.KC.BM.Max2.r11] I []
#bm_mul4 CFSG.KC.BM.Fu cdi CFSG.KC.BM.Max2.r4 [di] I []
#bm_mul4 CFSG.KC.BM.Fu cq0 CFSG.KC.BM.Max2.r4 [CFSG.KC.BM.Max2.r11] q0 []
#bm_mul4 CFSG.KC.BM.Fu cq1 di [CFSG.KC.BM.Max2.r11] q1 []
#bm_mul4 CFSG.KC.BM.Fu cq2 CFSG.KC.BM.Max2.r4 [q0] q2 []
#bm_mul4 CFSG.KC.BM.Fu cq3 di [q1] q3 []
#bm_mul4 CFSG.KC.BM.Fu cq4 q1 [q0] q4 []
#bm_mul4 CFSG.KC.BM.Fu cq5 q2 [q0] q5 []
#bm_mul4 CFSG.KC.BM.Fu cq6 di [q3] q6 []
#bm_mul4 CFSG.KC.BM.Fu cq7 CFSG.KC.BM.Fi23.img9 [Vi] q7 []
#bm_mul4 CFSG.KC.BM.Fu cq8 CFSG.KC.BM.Fi23.img1 [CFSG.KC.BM.Fi23.U] q8 []
#bm_mul4 CFSG.KC.BM.Fu cq9 CFSG.KC.BM.Fi23.V [CFSG.KC.BM.Fi23.img6] q9 []
#bm_mul4 CFSG.KC.BM.Fu cq10 CFSG.KC.BM.Fi23.img4 [CFSG.KC.BM.Fi23.img5] q10 []
#bm_mul4 CFSG.KC.BM.Fu cq11 CFSG.KC.BM.Fi23.img7 [Vi] q11 []
#bm_mul4 CFSG.KC.BM.Fu cq12 CFSG.KC.BM.Fi23.img3 [CFSG.KC.BM.Fi23.img7] q12 []
#bm_mul4 CFSG.KC.BM.Fu cq14 q6 [q4] q14 []
#bm_mul4 CFSG.KC.BM.Fu cq15 q0 [q5] q15 []
