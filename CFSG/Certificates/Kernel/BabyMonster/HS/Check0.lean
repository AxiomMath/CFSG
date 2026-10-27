module

import CFSG.Certificates.Kernel.BabyMonster.Load
import CFSG.Certificates.Kernel.BabyMonster.LoadFour
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
public import CFSG.Certificates.Kernel.BabyMonster.FiveM.Data0
public import CFSG.Certificates.Kernel.BabyMonster.HS.Data0

#bm_mul4 CFSG.KC.BM.HS c_y2 CFSG.KC.BM.FiveM.y [CFSG.KC.BM.FiveM.y] y2 []
#bm_mul4 CFSG.KC.BM.HS c_y1p2 CFSG.KC.BM.FiveM.y1 [CFSG.KC.BM.FiveM.y1] y1p2 []
#bm_mul4 CFSG.KC.BM.HS c_y1p3 y1p2 [CFSG.KC.BM.FiveM.y1] y1p3 []
#bm_mul4 CFSG.KC.BM.HS c_y1p6 y1p3 [y1p3] y1p6 []
#bm_mul4 CFSG.KC.BM.HS c_y1p9 y1p6 [y1p3] y1p9 []
#bm_mul4 CFSG.KC.BM.HS c_y1p12 y1p6 [y1p6] y1p12 []
#bm_mul4 CFSG.KC.BM.HS c_a y2 [y1p12] a []
#bm_mul4 CFSG.KC.BM.HS c_b CFSG.KC.BM.FiveM.y [y1p9] b []
#bm_mul4 CFSG.KC.BM.HS c_x1 a [b] x1 []
#bm_mul4 CFSG.KC.BM.HS c_x2 x1 [b] x2 []
