module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
meta import CFSG.Certificates.Kernel.BabyMonster.TwinDy
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data1
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data4
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data3
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.BabyMonster.Load

#kc_repo #bm_mat CFSG.KC.BM.Max2 Yz
  "CFSG/Certificates/Kernel/BabyMonster/Max2/data/Yz.bin" 2412240 2015583800763558245
#kc_repo #bm_mat CFSG.KC.BM.Max2 Yz_sq1
  "CFSG/Certificates/Kernel/BabyMonster/Max2/data/Yz_sq1.bin" 2412240 9515412763979390511
#kc_repo #bm_mat CFSG.KC.BM.Max2 Yz_sq2
  "CFSG/Certificates/Kernel/BabyMonster/Max2/data/Yz_sq2.bin" 2412240 10125862448021737455
#kc_repo #bm_mat CFSG.KC.BM.Max2 Y3
  "CFSG/Certificates/Kernel/BabyMonster/Max2/data/Y3.bin" 2412240 14995941638699610848
#kc_repo #bm_mat CFSG.KC.BM.Max2 U
  "CFSG/Certificates/Kernel/BabyMonster/Max2/data/U.bin" 2412240 3280705747674666867
#kc_eval CFSG.KC.BM.Max2 U_inv CFSG.KC.BM.Twin.inv 4370 0 0 U
#kc_repo #bm_mat CFSG.KC.BM.Max2 C
  "CFSG/Certificates/Kernel/BabyMonster/Max2/data/C.bin" 2412240 2153002511236677101
#kc_eval CFSG.KC.BM.Max2 C_inv CFSG.KC.BM.Twin.inv 4370 0 0 C
#kc_repo #bm_rows CFSG.KC.BM.Max2 C
  "CFSG/Certificates/Kernel/BabyMonster/Max2/data/C.rows" 2412240 5685327359288671629
#kc_repo #bm_mat CFSG.KC.BM.Max2 Ci
  "CFSG/Certificates/Kernel/BabyMonster/Max2/data/Ci.bin" 2412240 2404692629038087389
#kc_repo #bm_rows CFSG.KC.BM.Max2 Ci
  "CFSG/Certificates/Kernel/BabyMonster/Max2/data/Ci.rows" 2412240 11786187567781708078
#kc_repo #bm_mat CFSG.KC.BM.Max2 G1
  "CFSG/Certificates/Kernel/BabyMonster/Max2/data/G1.bin" 2412240 8320937873484631743
#kc_repo #bm_rows CFSG.KC.BM.Max2 G1
  "CFSG/Certificates/Kernel/BabyMonster/Max2/data/G1.rows" 2412240 1489016377335094383
