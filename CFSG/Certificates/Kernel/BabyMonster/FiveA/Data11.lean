module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
meta import CFSG.Certificates.Kernel.BabyMonster.TwinRank
import CFSG.Certificates.Kernel.BabyMonster.Five.Data14
import CFSG.Certificates.Kernel.BabyMonster.Five.Data18
import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data14

#kc_eval CFSG.KC.BM.FiveA v70a CFSG.KC.BM.Twin.prod 4370 0 0 p2 CFSG.KC.BM.Five.f85 CFSG.KC.BM.Five.oh_p
#kc_eval CFSG.KC.BM.FiveA v70b CFSG.KC.BM.Twin.prod 4370 0 0 v70a CFSG.KC.BM.Five.f85 CFSG.KC.BM.Five.f86
#kc_eval CFSG.KC.BM.FiveA v70c CFSG.KC.BM.Twin.prod 4370 0 0 v70b CFSG.KC.BM.Five.f85_sq2 CFSG.KC.BM.Five.oh_p
#kc_eval CFSG.KC.BM.FiveA v70d CFSG.KC.BM.Twin.prod 4370 0 0 v70c CFSG.KC.BM.Five.f85 p2
#kc_eval CFSG.KC.BM.FiveA v70 CFSG.KC.BM.Twin.prod 4370 0 0 v70d CFSG.KC.BM.Five.f85_sq1 CFSG.KC.BM.Five.oh_p
#kc_eval CFSG.KC.BM.FiveA PrkT CFSG.KC.BM.Twin.rank 4370 0 0 CFSG.KC.BM.Five.f86_sq2 1 1
