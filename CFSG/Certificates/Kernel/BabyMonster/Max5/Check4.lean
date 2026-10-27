module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.Max5.Data0
public import CFSG.Certificates.Kernel.BabyMonster.Max5.Data1
public import CFSG.Certificates.Kernel.BabyMonster.Max5.Data2
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0

#bm_mul CFSG.KC.BM.Max5 cm12 m1 [m11] m12 []
#bm_mul CFSG.KC.BM.Max5 cm13 m12 [m13] I []
#bm_bool CFSG.KC.BM.Max5 wf_m13 (CFSG.KC.BM.wfMat m13)
#bm_mul CFSG.KC.BM.Max5 cm14 m13 [CFSG.KC.BM.Seeds.A2] m14 []
