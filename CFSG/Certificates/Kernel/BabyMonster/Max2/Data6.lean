module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
meta import CFSG.Certificates.Kernel.BabyMonster.TwinDy
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data0
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data5
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data0
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data1
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data2
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data3

#kc_eval CFSG.KC.BM.Max2 G2 CFSG.KC.BM.Twin.prod 4370 2412240 1952356317998132724 C r4 C_inv
#kc_eval CFSG.KC.BM.Max2 G2 CFSG.KC.BM.Twin.rowsOf 4370 2412240 14124201994271181359 G2
#kc_eval CFSG.KC.BM.Max2 Gi2 CFSG.KC.BM.Twin.inv 4370 2412240 7390504070628090846 G2
#kc_eval CFSG.KC.BM.Max2 Gi2 CFSG.KC.BM.Twin.rowsOf 4370 2412240 13640837381568955692 Gi2
#kc_eval CFSG.KC.BM.Max2 E1 CFSG.KC.BM.Twin.prod 4370 2412240 538580143122678004 CFSG.KC.BM.NativePair.Q24_inv CFSG.KC.BM.NativePair.Q0 CFSG.KC.BM.NativePair.Q24
#kc_eval CFSG.KC.BM.Max2 E1 CFSG.KC.BM.Twin.rowsOf 4370 2412240 9747250055596425649 E1
#kc_eval CFSG.KC.BM.Max2 E2 CFSG.KC.BM.Twin.prod 4370 2412240 16711386112401531022 CFSG.KC.BM.NativePair.Q14_inv E1 CFSG.KC.BM.NativePair.Q14
#kc_eval CFSG.KC.BM.Max2 E2 CFSG.KC.BM.Twin.rowsOf 4370 2412240 766100917612348383 E2
#kc_eval CFSG.KC.BM.Max2 E3 CFSG.KC.BM.Twin.prod 4370 2412240 5895461231375835799 CFSG.KC.BM.NativePair.Q24_inv E2 CFSG.KC.BM.NativePair.Q24
#kc_eval CFSG.KC.BM.Max2 E3 CFSG.KC.BM.Twin.rowsOf 4370 2412240 579100316764613107 E3
#kc_eval CFSG.KC.BM.Max2 E4_0 CFSG.KC.BM.Twin.prod 4370 2412240 5895461231375835799 CFSG.KC.BM.NativePair.Q22_inv E3 CFSG.KC.BM.NativePair.Q22
#kc_eval CFSG.KC.BM.Max2 E4_1 CFSG.KC.BM.Twin.prod 4370 2412240 16711386112401531022 CFSG.KC.BM.NativePair.Q24_inv E4_0 CFSG.KC.BM.NativePair.Q24
#kc_eval CFSG.KC.BM.Max2 E4 CFSG.KC.BM.Twin.prod 4370 2412240 7333162057489985605 CFSG.KC.BM.NativePair.Q7_inv E4_1 CFSG.KC.BM.NativePair.Q7
#kc_eval CFSG.KC.BM.Max2 E4 CFSG.KC.BM.Twin.rowsOf 4370 2412240 1248400132574032822 E4
