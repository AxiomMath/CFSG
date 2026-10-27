module

import CFSG.Certificates.Kernel.BabyMonster.LoadFour
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Data0
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Data4
public import CFSG.Certificates.Kernel.BabyMonster.FiveM.Data0

#bm_mul4 CFSG.KC.BM.FiveM cq4 CFSG.KC.BM.Max15.r16 [CFSG.KC.BM.Max15.r16] q4 []
#bm_mul4 CFSG.KC.BM.FiveM cq8 q4 [q4] q8 []
#bm_mul4 CFSG.KC.BM.FiveM cq12 q8 [q4] q12 []
#bm_mul4 CFSG.KC.BM.FiveM cs q12 [CFSG.KC.BM.Max15.r16] s []
#bm_mul4 CFSG.KC.BM.FiveM cy s [CFSG.KC.BM.Max15.g2] y []
#bm_mul4 CFSG.KC.BM.FiveM cs2 s [s] s2 []
#bm_mul4 CFSG.KC.BM.FiveM cs4 s2 [s2] s4 []
#bm_mul4 CFSG.KC.BM.FiveM cg1c CFSG.KC.BM.Max15.g1 [CFSG.KC.BM.Max15.g1 CFSG.KC.BM.Max15.g1] g1c []
#bm_mul4 CFSG.KC.BM.FiveM cy1 CFSG.KC.BM.Max15.g1 [y g1c] y1 []
#bm_mul4 CFSG.KC.BM.FiveM cw y1 [y] w []
#bm_mul4 CFSG.KC.BM.FiveM cw2 w [w] w2 []
#bm_mul4 CFSG.KC.BM.FiveM cw4 w2 [w2] w4 []
#bm_mul4 CFSG.KC.BM.FiveM ca w4 [w] a []
#bm_mul4 CFSG.KC.BM.FiveM cv y [y1] v []
#bm_mul4 CFSG.KC.BM.FiveM cv2 v [v] v2 []
#bm_mul4 CFSG.KC.BM.FiveM cv4 v2 [v2] v4 []
#bm_mul4 CFSG.KC.BM.FiveM cb v4 [v] b []
#bm_mul4 CFSG.KC.BM.FiveM cab a [b] ab []
#bm_mul4 CFSG.KC.BM.FiveM cas a [s] aS []
#bm_mul4 CFSG.KC.BM.FiveM sfive s4 [s] I []
#bm_mul4 CFSG.KC.BM.FiveM asq a [a] I []
#bm_mul4 CFSG.KC.BM.FiveM ba b [a] ab []
#bm_mul4 CFSG.KC.BM.FiveM sa s [a] aS []
