module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data2
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data4
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data5
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data3
import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0

#kc_eval CFSG.KC.BM.Transfer Xp CFSG.KC.BM.Twin.prod 4370 2412240 8855014924575939642 CFSG.KC.BM.NativePair.Q25 CFSG.KC.BM.NativePair.Q25 CFSG.KC.BM.Max2.Xb CFSG.KC.BM.NativePair.Q25
#kc_eval CFSG.KC.BM.Transfer Wq CFSG.KC.BM.Twin.prod 4370 2412240 2701207410496464558 CFSG.KC.BM.Seeds.A2 CFSG.KC.BM.Seeds.A2 CFSG.KC.BM.Max2.R4 CFSG.KC.BM.Seeds.A2
#kc_eval CFSG.KC.BM.Transfer Yq CFSG.KC.BM.Twin.prod 4370 2412240 8113067374477435526 CFSG.KC.BM.Max2.Ci Xp CFSG.KC.BM.Max2.C
#kc_eval CFSG.KC.BM.Transfer WY CFSG.KC.BM.Twin.prod 4370 2412240 2099266488907192688 Wq Yq
#kc_eval CFSG.KC.BM.Transfer WY_sq1 CFSG.KC.BM.Twin.prod 4370 2412240 6257329225964298801 WY WY
#kc_eval CFSG.KC.BM.Transfer WY_sq2 CFSG.KC.BM.Twin.prod 4370 2412240 8961439492232329195 WY_sq1 WY_sq1
#kc_eval CFSG.KC.BM.Transfer DW CFSG.KC.BM.Twin.prod 4370 2412240 6735510334678708638 CFSG.KC.BM.Max2.R4 Wq
#kc_eval CFSG.KC.BM.Transfer DW_sq1 CFSG.KC.BM.Twin.prod 4370 2412240 2725502521023674535 DW DW
