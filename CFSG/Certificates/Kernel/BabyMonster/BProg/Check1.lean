module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Data0
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Data1
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Data2
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Data3
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Data4
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Data5
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Data6
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Data7
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Data8
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Data9
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Data10
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Data11
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Data12
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0

#bm_mul CFSG.KC.BM.BProg c_b3m2 b3q1 [b3q4] b3m2 []
#bm_mul CFSG.KC.BM.BProg c_t11 b2 [b3m2] t11 []
#bm_mul CFSG.KC.BM.BProg c_b4 CFSG.KC.BM.Seeds.A1 [t11] b4 []
#bm_mul CFSG.KC.BM.BProg c_b5q1 b4 [b4] b5q1 []
#bm_mul CFSG.KC.BM.BProg c_b5 b4 [b5q1] b5 []
#bm_mul CFSG.KC.BM.BProg c_b6q1 CFSG.KC.BM.Seeds.A2 [CFSG.KC.BM.Seeds.A2] b6q1 []
#bm_mul CFSG.KC.BM.BProg c_b7 b6q1 [CFSG.KC.BM.Seeds.A1] b7 []
#bm_mul CFSG.KC.BM.BProg c_b8q1 b7 [b7] b8q1 []
#bm_mul CFSG.KC.BM.BProg c_b8q2 b8q1 [b8q1] b8q2 []
#bm_mul CFSG.KC.BM.BProg c_b8q3 b8q2 [b8q2] b8q3 []
#bm_mul CFSG.KC.BM.BProg c_b8m3 b8q2 [b8q3] b8m3 []
#bm_mul CFSG.KC.BM.BProg c_b8m2 b8q1 [b8m3] b8m2 []
