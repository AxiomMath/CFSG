module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Five.Data14
import CFSG.Certificates.Kernel.BabyMonster.Five.Data18
import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data14

#kc_eval CFSG.KC.BM.FiveA p68 CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Five.f85 CFSG.KC.BM.Five.f85_sq1
#kc_eval CFSG.KC.BM.FiveA v99a CFSG.KC.BM.Twin.prod 4370 0 0 p2 CFSG.KC.BM.Five.f85 CFSG.KC.BM.Five.oh_p
#kc_eval CFSG.KC.BM.FiveA v99b CFSG.KC.BM.Twin.prod 4370 0 0 v99a CFSG.KC.BM.Five.f85 CFSG.KC.BM.Five.f86
#kc_eval CFSG.KC.BM.FiveA v99c CFSG.KC.BM.Twin.prod 4370 0 0 v99b CFSG.KC.BM.Five.f85 CFSG.KC.BM.Five.f86_sq1
#kc_eval CFSG.KC.BM.FiveA v99d CFSG.KC.BM.Twin.prod 4370 0 0 v99c CFSG.KC.BM.Five.f85_sq2 CFSG.KC.BM.Five.f86
#kc_eval CFSG.KC.BM.FiveA v99 CFSG.KC.BM.Twin.prod 4370 0 0 v99d CFSG.KC.BM.Five.f85_sq2 CFSG.KC.BM.Five.oh_p
