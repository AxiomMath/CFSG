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

#bm_mul CFSG.KC.BM.BProg c_b0 CFSG.KC.BM.Seeds.A1 [CFSG.KC.BM.Seeds.A2] b0 []
#bm_mul CFSG.KC.BM.BProg c_b1q1 b0 [b0] b1q1 []
#bm_mul CFSG.KC.BM.BProg c_b1q2 b1q1 [b1q1] b1q2 []
#bm_mul CFSG.KC.BM.BProg c_b1q3 b1q2 [b1q2] b1q3 []
#bm_mul CFSG.KC.BM.BProg c_b1m3 b1q2 [b1q3] b1m3 []
#bm_mul CFSG.KC.BM.BProg c_b1m2 b1q1 [b1m3] b1m2 []
#bm_mul CFSG.KC.BM.BProg c_b1 b0 [b1m2] b1 []
#bm_mul CFSG.KC.BM.BProg c_b2 b1 [CFSG.KC.BM.Seeds.A2] b2 []
#bm_mul CFSG.KC.BM.BProg c_b3q1 b2 [b2] b3q1 []
#bm_mul CFSG.KC.BM.BProg c_b3q2 b3q1 [b3q1] b3q2 []
#bm_mul CFSG.KC.BM.BProg c_b3q3 b3q2 [b3q2] b3q3 []
#bm_mul CFSG.KC.BM.BProg c_b3q4 b3q3 [b3q3] b3q4 []
