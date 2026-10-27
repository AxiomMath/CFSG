module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Three.Data4

#kc_eval CFSG.KC.BM.Three t37 CFSG.KC.BM.Twin.prod 4370 2412240 2533635178711924006 t32 t35
#kc_eval CFSG.KC.BM.Three t37_sq1 CFSG.KC.BM.Twin.prod 4370 2412240 14562558567729832418 t37 t37
#kc_eval CFSG.KC.BM.Three t37_sq2 CFSG.KC.BM.Twin.prod 4370 2412240 6077993541748612208 t37_sq1 t37_sq1
#kc_eval CFSG.KC.BM.Three t38 CFSG.KC.BM.Twin.prod 4370 2412240 14813680490004122814 t37 t37_sq2
#kc_eval CFSG.KC.BM.Three t48 CFSG.KC.BM.Twin.inv 4370 2412240 2573133042245164936 t38
