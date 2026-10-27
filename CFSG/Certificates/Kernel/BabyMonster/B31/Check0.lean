module

import CFSG.Certificates.Kernel.BabyMonster.Load
import CFSG.Certificates.Kernel.BabyMonster.LoadFour
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0
public import CFSG.Certificates.Kernel.BabyMonster.Max5.Data0
public import CFSG.Certificates.Kernel.BabyMonster.Max5.Data1
public import CFSG.Certificates.Kernel.BabyMonster.Max5.Data2
public import CFSG.Certificates.Kernel.BabyMonster.B31.Data0

#bm_mul4 CFSG.KC.BM.B31 c_n0 CFSG.KC.BM.Max5.m16 [CFSG.KC.BM.Max5.m1] n0 []
#bm_mul4 CFSG.KC.BM.B31 c_n1 n0 [n0] n1 []
#bm_mul4 CFSG.KC.BM.B31 c_n2 n1 [n1] n2 []
#bm_mul4 CFSG.KC.BM.B31 c_n3 CFSG.KC.BM.Max5.m0 [CFSG.KC.BM.Max5.m20] n3 []
#bm_mul4 CFSG.KC.BM.B31 c_n4 n3 [n3] n4 []
#bm_mul4 CFSG.KC.BM.B31 c_n5 n2 [n1 n2] n5 []
#bm_mul4 CFSG.KC.BM.B31 c_n6 n3 [n4 n5 CFSG.KC.BM.Max5.m20] n6 []
#bm_mul4 CFSG.KC.BM.B31 c_n7 CFSG.KC.BM.Max5.m13 [CFSG.KC.BM.Seeds.A2 CFSG.KC.BM.Max5.m12] n7 []
#bm_mul4 CFSG.KC.BM.B31 c_n8 n6 [n7] n8 []
#bm_mul4 CFSG.KC.BM.B31 c_n9 n7 [n8] n9 []
#bm_mul4 CFSG.KC.BM.B31 c_n10 n7 [n7] n10 []
#bm_mul4 CFSG.KC.BM.B31 c_n11 n10 [n6] n11 []
