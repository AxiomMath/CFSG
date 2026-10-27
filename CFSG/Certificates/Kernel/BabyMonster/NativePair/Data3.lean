module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data0
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data1
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data2
import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0
meta import CFSG.Certificates.Kernel.BabyMonster.TwinDy
meta import CFSG.Certificates.Kernel.BabyMonster.TwinRank
import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Basis
import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Gens
import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Data7
import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Extra

#kc_eval CFSG.KC.BM.NativePair Q24 CFSG.KC.BM.Twin.quotRows 4370 0 2412240 8437174290072815573 CFSG.KC.BM.FixedLine.Q24.rows
#kc_eval CFSG.KC.BM.NativePair Q24 CFSG.KC.BM.Twin.stripsOf 4370 2412240 8919185072209989534 Q24.rows
#kc_eval CFSG.KC.BM.NativePair Q24_inv CFSG.KC.BM.Twin.inv 4370 0 0 Q24
#kc_eval CFSG.KC.BM.NativePair Q25 CFSG.KC.BM.Twin.quotRows 4370 0 2412240 11433447387010198752 CFSG.KC.BM.FixedLine.Q25.rows
#kc_eval CFSG.KC.BM.NativePair Q25 CFSG.KC.BM.Twin.stripsOf 4370 2412240 9744766227205405551 Q25.rows
#kc_eval CFSG.KC.BM.NativePair F0 CFSG.KC.BM.Twin.dyMono 2412240 12562931397618528084 1197 CFSG.KC.BM.FixedLine.f CFSG.KC.BM.Dyadic.Bs CFSG.KC.BM.Dyadic.M26 CFSG.KC.BM.Dyadic.G26
#kc_repo #kc_natBin CFSG.KC.BM.NativePair Tb64 "CFSG/Monster/B/Data/intertwiner-T.b64" 3216342 15087119441404597270
#kc_eval CFSG.KC.BM.NativePair T CFSG.KC.BM.Twin.b64Rows 4370 0 2412256 6839754000974149469 Tb64
#kc_eval CFSG.KC.BM.NativePair T CFSG.KC.BM.Twin.stripsOf 4370 2412240 4811354702957972348 T.rows
#kc_eval CFSG.KC.BM.NativePair T_inv CFSG.KC.BM.Twin.inv 4370 0 0 T
#kc_eval CFSG.KC.BM.NativePair F CFSG.KC.BM.Twin.prod 4370 2412240 9725580437268926338 T CFSG.KC.BM.Seeds.A1 T_inv
#kc_eval CFSG.KC.BM.NativePair F CFSG.KC.BM.Twin.rowsOf 4370 2412240 8821441492314525807 F
#kc_eval CFSG.KC.BM.NativePair W_0 CFSG.KC.BM.Twin.prod 4370 2412240 15865971971325330255 Q2 Q16 Q11 Q25
#kc_eval CFSG.KC.BM.NativePair W_1 CFSG.KC.BM.Twin.prod 4370 2412240 11306754891821821408 W_0 Q2 Q4 Q16
#kc_eval CFSG.KC.BM.NativePair W_2 CFSG.KC.BM.Twin.prod 4370 2412240 3349743748537042506 W_1 Q14 Q1 Q10
