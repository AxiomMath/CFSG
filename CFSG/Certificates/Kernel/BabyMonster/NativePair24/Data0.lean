module

import CFSG.Certificates.Kernel.Common.Eval
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
meta import CFSG.Certificates.Kernel.BabyMonster.TwinDy
meta import CFSG.Certificates.Kernel.BabyMonster.TwinRank
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data0
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data1
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data2
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data3
import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0

#kc_repo #kc_natBin CFSG.KC.BM.NativePair24 Tb64 "CFSG/Monster/B/Data/intertwiner-T24.b64" 3216342 5299499733572732127
#kc_eval CFSG.KC.BM.NativePair24 T CFSG.KC.BM.Twin.b64Rows 4370 0 2412256 14426599361094611286 Tb64
#kc_eval CFSG.KC.BM.NativePair24 T CFSG.KC.BM.Twin.stripsOf 4370 2412240 3601680516470149489 T.rows
#kc_eval CFSG.KC.BM.NativePair24 T_inv CFSG.KC.BM.Twin.inv 4370 0 0 T
#kc_eval CFSG.KC.BM.NativePair24 F CFSG.KC.BM.Twin.prod 4370 2412240 4732521747741004641 T CFSG.KC.BM.Seeds.A1 T_inv
#kc_eval CFSG.KC.BM.NativePair24 F CFSG.KC.BM.Twin.rowsOf 4370 2412240 16379887693894457319 F
#kc_eval CFSG.KC.BM.NativePair24 W_0 CFSG.KC.BM.Twin.prod 4370 2412240 5516947619560812454 CFSG.KC.BM.NativePair.Q17 CFSG.KC.BM.NativePair.Q3 CFSG.KC.BM.NativePair.Q17 CFSG.KC.BM.NativePair.Q18
#kc_eval CFSG.KC.BM.NativePair24 W_1 CFSG.KC.BM.Twin.prod 4370 2412240 16790556524765960688 W_0 CFSG.KC.BM.NativePair.Q21 CFSG.KC.BM.NativePair.Q23 CFSG.KC.BM.NativePair.Q25
