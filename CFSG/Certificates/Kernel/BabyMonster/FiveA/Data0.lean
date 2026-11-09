module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
meta import CFSG.Certificates.Kernel.BabyMonster.TwinRank
import CFSG.Certificates.Kernel.BabyMonster.Five.Data3
import CFSG.Certificates.Kernel.BabyMonster.Five.Data4
import CFSG.Certificates.Kernel.BabyMonster.Five.Data12
import CFSG.Certificates.Kernel.BabyMonster.Five.Data14
import CFSG.Certificates.Kernel.BabyMonster.Five.Data18
import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data11
import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data14
import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data15

#kc_eval CFSG.KC.BM.FiveA a1 CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Five.f85 CFSG.KC.BM.Five.f86_sq2 CFSG.KC.BM.Five.f85_sq2
#kc_eval CFSG.KC.BM.FiveA a3a CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Five.oh_p a1 p2
#kc_eval CFSG.KC.BM.FiveA a3b CFSG.KC.BM.Twin.prod 4370 0 0 a3a a1 CFSG.KC.BM.Five.H3
#kc_eval CFSG.KC.BM.FiveA a3 CFSG.KC.BM.Twin.prod 4370 0 0 a3b a1 CFSG.KC.BM.Five.f86_sq2
#kc_eval CFSG.KC.BM.FiveA b5 CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Five.f86_sq2 b4
#kc_eval CFSG.KC.BM.FiveA p28 CFSG.KC.BM.Twin.prod 4370 0 0 v27 v27
#kc_eval CFSG.KC.BM.FiveA p29 CFSG.KC.BM.Twin.prod 4370 0 0 p28 p28
#kc_eval CFSG.KC.BM.FiveA p30 CFSG.KC.BM.Twin.prod 4370 0 0 p28 v27
#kc_eval CFSG.KC.BM.FiveA e42 CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Five.W_sq3 CFSG.KC.BM.Five.Q3 CFSG.KC.BM.Five.Q4_sq1
#kc_eval CFSG.KC.BM.FiveA c43 CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Five.f86_sq2 e42
#kc_eval CFSG.KC.BM.FiveA RrkT CFSG.KC.BM.Twin.polyMul 4370 0 0 PrkT CFSG.KC.BM.Five.f86_sq2 1 1
#kc_eval CFSG.KC.BM.FiveA PrkU CFSG.KC.BM.Twin.rank 4370 0 0 a3 1 1
#kc_eval CFSG.KC.BM.FiveA RrkU CFSG.KC.BM.Twin.polyMul 4370 0 0 PrkU a3 1 1
