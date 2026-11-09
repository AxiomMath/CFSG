module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Five.Data4
import CFSG.Certificates.Kernel.BabyMonster.Five.Data14
import CFSG.Certificates.Kernel.BabyMonster.Five.Data18
import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data14

#kc_eval CFSG.KC.BM.FiveA v8a CFSG.KC.BM.Twin.prod 4370 0 0 p2 CFSG.KC.BM.Five.f85 CFSG.KC.BM.Five.oh_p
#kc_eval CFSG.KC.BM.FiveA v8b CFSG.KC.BM.Twin.prod 4370 0 0 v8a CFSG.KC.BM.Five.f85 CFSG.KC.BM.Five.f86_sq1
#kc_eval CFSG.KC.BM.FiveA v8c CFSG.KC.BM.Twin.prod 4370 0 0 v8b CFSG.KC.BM.Five.f85_sq2 CFSG.KC.BM.Five.f86
#kc_eval CFSG.KC.BM.FiveA v8d CFSG.KC.BM.Twin.prod 4370 0 0 v8c CFSG.KC.BM.Five.f85 p2
#kc_eval CFSG.KC.BM.FiveA v8 CFSG.KC.BM.Twin.prod 4370 0 0 v8d CFSG.KC.BM.Five.Q4_sq2
#kc_eval CFSG.KC.BM.FiveA p9 CFSG.KC.BM.Twin.prod 4370 0 0 v8 v8
#kc_eval CFSG.KC.BM.FiveA p10 CFSG.KC.BM.Twin.prod 4370 0 0 p9 p9
#kc_eval CFSG.KC.BM.FiveA p11 CFSG.KC.BM.Twin.prod 4370 0 0 p10 v8
