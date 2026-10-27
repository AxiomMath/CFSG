module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
meta import CFSG.Certificates.Kernel.BabyMonster.TwinDy
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data1
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data4
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data3

#kc_eval CFSG.KC.BM.Max2 Yz CFSG.KC.BM.Twin.prod 4370 2412240 2015583800763558245 Zw Xb
#kc_eval CFSG.KC.BM.Max2 Yz_sq1 CFSG.KC.BM.Twin.prod 4370 2412240 9515412763979390511 Yz Yz
#kc_eval CFSG.KC.BM.Max2 Yz_sq2 CFSG.KC.BM.Twin.prod 4370 2412240 10125862448021737455 Yz_sq1 Yz_sq1
#kc_eval CFSG.KC.BM.Max2 Y3 CFSG.KC.BM.Twin.prod 4370 2412240 14995941638699610848 Yz Yz Yz
#kc_eval CFSG.KC.BM.Max2 U CFSG.KC.BM.Twin.prod 4370 2412240 3280705747674666867 Wp Y3
#kc_eval CFSG.KC.BM.Max2 U_inv CFSG.KC.BM.Twin.inv 4370 0 0 U
#kc_eval CFSG.KC.BM.Max2 C CFSG.KC.BM.Twin.prod 4370 2412240 2153002511236677101 U_inv CFSG.KC.BM.NativePair.T
#kc_eval CFSG.KC.BM.Max2 C_inv CFSG.KC.BM.Twin.inv 4370 0 0 C
#kc_eval CFSG.KC.BM.Max2 C CFSG.KC.BM.Twin.rowsOf 4370 2412240 5685327359288671629 C
#kc_eval CFSG.KC.BM.Max2 Ci CFSG.KC.BM.Twin.prod 4370 2412240 2404692629038087389 C_inv
#kc_eval CFSG.KC.BM.Max2 Ci CFSG.KC.BM.Twin.rowsOf 4370 2412240 11786187567781708078 Ci
#kc_eval CFSG.KC.BM.Max2 G1 CFSG.KC.BM.Twin.prod 4370 2412240 8320937873484631743 C r11 C_inv
#kc_eval CFSG.KC.BM.Max2 G1 CFSG.KC.BM.Twin.rowsOf 4370 2412240 1489016377335094383 G1
