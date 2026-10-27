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

#bm_mul CFSG.KC.BM.MultSeven c_b37q2 b37q1 [b37q1] b37q2 []
#bm_mul CFSG.KC.BM.MultSeven c_b37q3 b37q2 [b37q2] b37q3 []
#bm_mul CFSG.KC.BM.MultSeven c_b37q4 b37q3 [b37q3] b37q4 []
#bm_mul CFSG.KC.BM.MultSeven c_b37 b34 [b37q4] b37 []
#bm_mul CFSG.KC.BM.MultSeven c_b38 CFSG.KC.BM.Max5.m15 [b34] b38 []
#bm_mul CFSG.KC.BM.MultSeven c_h3 b37 [b38] h3 []
