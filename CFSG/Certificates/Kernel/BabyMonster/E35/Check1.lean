module

import CFSG.Certificates.Kernel.BabyMonster.LoadFour
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
public import CFSG.Certificates.Kernel.BabyMonster.E35.Data0
public import CFSG.Certificates.Kernel.BabyMonster.E35.Data1
public import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data3

#bm_mul4 CFSG.KC.BM.E35 c_n5 CFSG.KC.BM.Fi23.g16 [m4] n5 []
#bm_mul4 CFSG.KC.BM.E35 c_n6 CFSG.KC.BM.Fi23.g16 [n5] n6 []
#bm_mul4 CFSG.KC.BM.E35 c_n3 n5 [m4] n3 []
#bm_mul4 CFSG.KC.BM.E35 c_n5b n6 [n3] n5b []
#bm_mul4 CFSG.KC.BM.E35 c_n4 n3 [n6] n4 []
#bm_mul4 CFSG.KC.BM.E35 c_h2 n5b [n4] h2 []
