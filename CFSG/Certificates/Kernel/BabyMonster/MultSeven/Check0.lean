module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.Max5.Data0
public import CFSG.Certificates.Kernel.BabyMonster.Max5.Data1
public import CFSG.Certificates.Kernel.BabyMonster.Max5.Data2
public import CFSG.Certificates.Kernel.BabyMonster.MultSeven.Data0
public import CFSG.Certificates.Kernel.BabyMonster.MultSeven.Data1
public import CFSG.Certificates.Kernel.BabyMonster.MultSeven.Data2
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0

#bm_mul CFSG.KC.BM.MultSeven c_b24 CFSG.KC.BM.Max5.m23 [CFSG.KC.BM.Max5.m15] b24 []
#bm_mul CFSG.KC.BM.MultSeven c_b25 b24 [CFSG.KC.BM.Max5.m15] b25 []
#bm_mul CFSG.KC.BM.MultSeven c_b26q1 b24 [b24] b26q1 []
#bm_mul CFSG.KC.BM.MultSeven c_b26q2 b26q1 [b26q1] b26q2 []
#bm_mul CFSG.KC.BM.MultSeven c_b27 b26q2 [b25] b27 []
#bm_mul CFSG.KC.BM.MultSeven c_b28q1 b25 [b25] b28q1 []
