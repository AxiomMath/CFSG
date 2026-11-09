module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.BabyMonster.Load

#kc_repo #bm_mat CFSG.KC.BM.Fi23 r20
  "CFSG/Certificates/Kernel/BabyMonster/Fi23/data/r20.bin" 2412240 14167023224937960939
#kc_repo #bm_mat CFSG.KC.BM.Fi23 r21
  "CFSG/Certificates/Kernel/BabyMonster/Fi23/data/r21.bin" 2412240 11387873632816781491
#kc_repo #bm_mat CFSG.KC.BM.Fi23 r22
  "CFSG/Certificates/Kernel/BabyMonster/Fi23/data/r22.bin" 2412240 9436571988541600944
#kc_eval CFSG.KC.BM.Fi23 ci23 CFSG.KC.BM.Twin.inv 4370 0 0 r22
#kc_repo #bm_mat CFSG.KC.BM.Fi23 U
  "CFSG/Certificates/Kernel/BabyMonster/Fi23/data/U.bin" 2412240 4484684034817280270
