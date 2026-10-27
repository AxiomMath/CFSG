module

import CFSG.Certificates.Kernel.BabyMonster.LoadFour
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
public import CFSG.Certificates.Kernel.BabyMonster.E35.Data1
public import CFSG.Certificates.Kernel.BabyMonster.E35.Data2
public import CFSG.Certificates.Kernel.BabyMonster.E35.Data3

#bm_mul4 CFSG.KC.BM.E35 c_wx q [ppq] wx []
#bm_mul4 CFSG.KC.BM.E35 c_wx2 wx [wx] wx2 []
#bm_mul4 CFSG.KC.BM.E35 c_wx3 wx2 [wx] wx3 []
#bm_mul4 CFSG.KC.BM.E35 c_x wx3 [wx3] x []
#bm_mul4 CFSG.KC.BM.E35 c_x2 x [x] x2 []
#bm_mul4 CFSG.KC.BM.E35 c_x1 gi [x g] x1 []
#bm_mul4 CFSG.KC.BM.E35 c_y2 gi [x1 g] y2 []
