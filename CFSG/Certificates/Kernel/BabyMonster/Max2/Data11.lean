module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data10
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data5

#kc_eval CFSG.KC.BM.Max2 S CFSG.KC.BM.Twin.prod 4370 2412240 17885868140236905024 S_1 G1
#kc_eval CFSG.KC.BM.Max2 S_sq1 CFSG.KC.BM.Twin.prod 4370 2412240 2194598527270589623 S S
#kc_eval CFSG.KC.BM.Max2 S_sq2 CFSG.KC.BM.Twin.prod 4370 2412240 16887274742472486392 S_sq1 S_sq1
#kc_eval CFSG.KC.BM.Max2 Kp0 CFSG.KC.BM.Twin.prod 4370 2412240 12993357432885781797 S_sq1 S_sq2
#kc_eval CFSG.KC.BM.Max2 S_sq3 CFSG.KC.BM.Twin.prod 4370 2412240 4778660217351032151 S_sq2 S_sq2
#kc_eval CFSG.KC.BM.Max2 K CFSG.KC.BM.Twin.prod 4370 2412240 10253630321602602980 Kp0 S_sq3
