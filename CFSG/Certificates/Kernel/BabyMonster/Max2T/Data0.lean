module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data2
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data4
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data5
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data0
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data1
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data2
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data3
import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Data0
import CFSG.Certificates.Kernel.BabyMonster.Max2Br.Data0
import CFSG.Certificates.Kernel.BabyMonster.Max2Br.Data1
import CFSG.Certificates.Kernel.BabyMonster.Max2Br.Data2

#kc_eval CFSG.KC.BM.Max2T Z CFSG.KC.BM.Twin.prod 4370 2412240 8705800744918647585 CFSG.KC.BM.NativePair24.T CFSG.KC.BM.Max2.R4 CFSG.KC.BM.NativePair24.T_inv
#kc_eval CFSG.KC.BM.Max2T Wp CFSG.KC.BM.Twin.prod 4370 2412240 16960707301364035127 CFSG.KC.BM.NativePair.Q12 CFSG.KC.BM.NativePair.Q25
#kc_eval CFSG.KC.BM.Max2T Wp_inv CFSG.KC.BM.Twin.inv 4370 0 0 Wp
#kc_eval CFSG.KC.BM.Max2T Zw CFSG.KC.BM.Twin.prod 4370 2412240 15450534652420936702 Wp_inv Z Wp
#kc_eval CFSG.KC.BM.Max2T Yz CFSG.KC.BM.Twin.prod 4370 2412240 8862617726695714224 Zw CFSG.KC.BM.Max2.Xb
#kc_eval CFSG.KC.BM.Max2T Yz_sq1 CFSG.KC.BM.Twin.prod 4370 2412240 12101721675959948830 Yz Yz
#kc_eval CFSG.KC.BM.Max2T Yz_sq2 CFSG.KC.BM.Twin.prod 4370 2412240 11159518550387465674 Yz_sq1 Yz_sq1
#kc_eval CFSG.KC.BM.Max2T Y3 CFSG.KC.BM.Twin.prod 4370 2412240 17147834070852843591 Yz_sq1 Yz
