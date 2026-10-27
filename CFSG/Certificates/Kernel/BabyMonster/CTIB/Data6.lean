module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
meta import CFSG.Certificates.Kernel.BabyMonster.TwinRank
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data5
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data6
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data7

#kc_eval CFSG.KC.BM.CTIB Pr9 CFSG.KC.BM.Twin.rank 4370 2412240 16588436834908997248 CFSG.KC.BM.Max2.G1.rows 1 1
#kc_eval CFSG.KC.BM.CTIB Qr9 CFSG.KC.BM.Twin.polyMul 4370 2412240 10657642067363069374 Pr9 CFSG.KC.BM.Max2.G1 1 1
#kc_eval CFSG.KC.BM.CTIB R10 CFSG.KC.BM.Twin.prod 4370 2412240 7413932249624891406 CFSG.KC.BM.Max2.G1 CFSG.KC.BM.Max2.E7
#kc_eval CFSG.KC.BM.CTIB Pr10 CFSG.KC.BM.Twin.rank 4370 2412240 1206385048468744283 R10 1 1
#kc_eval CFSG.KC.BM.CTIB Qr10 CFSG.KC.BM.Twin.polyMul 4370 2412240 6940149820809521677 Pr10 R10 1 1
#kc_eval CFSG.KC.BM.CTIB R11_0 CFSG.KC.BM.Twin.prod 4370 2412240 13920757430862173335 CFSG.KC.BM.Max2.G1 CFSG.KC.BM.Max2.E2 CFSG.KC.BM.Max2.E4
