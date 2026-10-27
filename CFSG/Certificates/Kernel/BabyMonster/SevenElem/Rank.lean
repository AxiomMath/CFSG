module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
meta import CFSG.Certificates.Kernel.BabyMonster.TwinRank
import CFSG.Certificates.Kernel.BabyMonster.Seven.Data1
import CFSG.Certificates.Kernel.BabyMonster.Seven.Data5
import CFSG.Certificates.Kernel.BabyMonster.SevenElem.Data0

#kc_eval CFSG.KC.BM.SevenElem PrkAl CFSG.KC.BM.Twin.rank 4370 0 0 CFSG.KC.BM.Seven.al 1 1
#kc_eval CFSG.KC.BM.SevenElem RrkAl CFSG.KC.BM.Twin.polyMul 4370 0 0 PrkAl CFSG.KC.BM.Seven.al 1 1
#kc_eval CFSG.KC.BM.SevenElem PrkT1 CFSG.KC.BM.Twin.rank 4370 0 0 CFSG.KC.BM.Seven.t1 1 1
#kc_eval CFSG.KC.BM.SevenElem RrkT1 CFSG.KC.BM.Twin.polyMul 4370 0 0 PrkT1 CFSG.KC.BM.Seven.t1 1 1
#kc_eval CFSG.KC.BM.SevenElem PrkT12 CFSG.KC.BM.Twin.rank 4370 0 0 t12 1 1
#kc_eval CFSG.KC.BM.SevenElem RrkT12 CFSG.KC.BM.Twin.polyMul 4370 0 0 PrkT12 t12 1 1
