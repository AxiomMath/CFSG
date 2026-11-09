module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
meta import CFSG.Certificates.Kernel.BabyMonster.TwinDy
meta import CFSG.Certificates.Kernel.BabyMonster.TwinRank
import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Basis
import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Gens
import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Extra
import CFSG.Certificates.Kernel.BabyMonster.Load

#kc_repo #bm_rows CFSG.KC.BM.NativePair Q24
  "CFSG/Certificates/Kernel/BabyMonster/NativePair/data/Q24.rows" 2412240 8437174290072815573
#kc_repo #bm_mat CFSG.KC.BM.NativePair Q24
  "CFSG/Certificates/Kernel/BabyMonster/NativePair/data/Q24.bin" 2412240 8919185072209989534
#kc_eval CFSG.KC.BM.NativePair Q24_inv CFSG.KC.BM.Twin.inv 4370 0 0 Q24
#kc_repo #bm_rows CFSG.KC.BM.NativePair Q25
  "CFSG/Certificates/Kernel/BabyMonster/NativePair/data/Q25.rows" 2412240 11433447387010198752
#kc_repo #bm_mat CFSG.KC.BM.NativePair Q25
  "CFSG/Certificates/Kernel/BabyMonster/NativePair/data/Q25.bin" 2412240 9744766227205405551
#kc_eval CFSG.KC.BM.NativePair F0 CFSG.KC.BM.Twin.dyMono 2412240 12562931397618528084 1197 CFSG.KC.BM.FixedLine.f CFSG.KC.BM.Dyadic.Bs CFSG.KC.BM.Dyadic.M26 CFSG.KC.BM.Dyadic.G26
#kc_repo #kc_natBin CFSG.KC.BM.NativePair Tb64 "CFSG/Monster/B/Data/intertwiner-T.b64" 3216342 15087119441404597270
#kc_eval CFSG.KC.BM.NativePair T CFSG.KC.BM.Twin.b64Rows 4370 0 2412256 6839754000974149469 Tb64
#kc_repo #bm_mat CFSG.KC.BM.NativePair T
  "CFSG/Certificates/Kernel/BabyMonster/NativePair/data/T.bin" 2412240 4811354702957972348
#kc_eval CFSG.KC.BM.NativePair T_inv CFSG.KC.BM.Twin.inv 4370 0 0 T
#kc_repo #bm_mat CFSG.KC.BM.NativePair F
  "CFSG/Certificates/Kernel/BabyMonster/NativePair/data/F.bin" 2412240 9725580437268926338
#kc_repo #bm_rows CFSG.KC.BM.NativePair F
  "CFSG/Certificates/Kernel/BabyMonster/NativePair/data/F.rows" 2412240 8821441492314525807
#kc_repo #bm_mat CFSG.KC.BM.NativePair W_0
  "CFSG/Certificates/Kernel/BabyMonster/NativePair/data/W_0.bin" 2412240 15865971971325330255
#kc_repo #bm_mat CFSG.KC.BM.NativePair W_1
  "CFSG/Certificates/Kernel/BabyMonster/NativePair/data/W_1.bin" 2412240 11306754891821821408
#kc_repo #bm_mat CFSG.KC.BM.NativePair W_2
  "CFSG/Certificates/Kernel/BabyMonster/NativePair/data/W_2.bin" 2412240 3349743748537042506
