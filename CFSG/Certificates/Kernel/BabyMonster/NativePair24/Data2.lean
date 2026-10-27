module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
meta import CFSG.Certificates.Kernel.BabyMonster.TwinDy
meta import CFSG.Certificates.Kernel.BabyMonster.TwinRank
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data0
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data1
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data2
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data3
import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0
import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Data0
import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Data1

#kc_eval CFSG.KC.BM.NativePair24 PF0 CFSG.KC.BM.Twin.rank 4370 2412240 6253128006857556748 CFSG.KC.BM.NativePair.F0.rows 1 1
#kc_eval CFSG.KC.BM.NativePair24 QF0 CFSG.KC.BM.Twin.polyMul 4370 2412240 4081900255283958449 PF0 F0 1 1
#kc_eval CFSG.KC.BM.NativePair24 AB CFSG.KC.BM.Twin.prod 4370 2412240 8331182325242170875 F CFSG.KC.BM.NativePair.Q25
#kc_eval CFSG.KC.BM.NativePair24 AB_sq1 CFSG.KC.BM.Twin.prod 4370 2412240 2373810026550860978 AB AB
#kc_eval CFSG.KC.BM.NativePair24 AB_sq2 CFSG.KC.BM.Twin.prod 4370 2412240 6427352135949883171 AB_sq1 AB_sq1
#kc_eval CFSG.KC.BM.NativePair24 oab_pp0 CFSG.KC.BM.Twin.prod 4370 2412240 4208346300161923242 AB_sq1 AB_sq2
#kc_eval CFSG.KC.BM.NativePair24 AB_sq3 CFSG.KC.BM.Twin.prod 4370 2412240 12669868133511964614 AB_sq2 AB_sq2
#kc_eval CFSG.KC.BM.NativePair24 AB_sq4 CFSG.KC.BM.Twin.prod 4370 2412240 12454313009311473468 AB_sq3 AB_sq3
