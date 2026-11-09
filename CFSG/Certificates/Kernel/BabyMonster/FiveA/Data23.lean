module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Five.Data4
import CFSG.Certificates.Kernel.BabyMonster.Five.Data12
import CFSG.Certificates.Kernel.BabyMonster.Five.Data16
import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data1
import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data2
import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data10

#kc_eval CFSG.KC.BM.FiveA v145 CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Five.Q4_sq2 CFSG.KC.BM.Five.Q2 CFSG.KC.BM.Five.Q4_sq2
#kc_eval CFSG.KC.BM.FiveA v146 CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Five.Q4 CFSG.KC.BM.Five.Q2_sq2 CFSG.KC.BM.Five.Q4
#kc_eval CFSG.KC.BM.FiveA v149 CFSG.KC.BM.Twin.prod 4370 0 0 v145 v99 v146
#kc_eval CFSG.KC.BM.FiveA v150 CFSG.KC.BM.Twin.prod 4370 0 0 v147 p11 v148
#kc_eval CFSG.KC.BM.FiveA v151 CFSG.KC.BM.Twin.prod 4370 0 0 v149 v150
#kc_eval CFSG.KC.BM.FiveA p152 CFSG.KC.BM.Twin.prod 4370 0 0 v151 v151
#kc_eval CFSG.KC.BM.FiveA p153 CFSG.KC.BM.Twin.prod 4370 0 0 p152 v151
#kc_eval CFSG.KC.BM.FiveA p154 CFSG.KC.BM.Twin.prod 4370 0 0 p153 p153
#kc_eval CFSG.KC.BM.FiveA p155 CFSG.KC.BM.Twin.prod 4370 0 0 p154 p154
#kc_eval CFSG.KC.BM.FiveA p156 CFSG.KC.BM.Twin.prod 4370 0 0 p155 v151
#kc_eval CFSG.KC.BM.FiveA v159 CFSG.KC.BM.Twin.prod 4370 0 0 v148 p156
