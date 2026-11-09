module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data1
import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data2
import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data15

#kc_eval CFSG.KC.BM.FiveA v104 CFSG.KC.BM.Twin.prod 4370 0 0 v101 p11 v102
#kc_eval CFSG.KC.BM.FiveA v105 CFSG.KC.BM.Twin.prod 4370 0 0 v103 v104
#kc_eval CFSG.KC.BM.FiveA p106 CFSG.KC.BM.Twin.prod 4370 0 0 v105 v105
#kc_eval CFSG.KC.BM.FiveA p107 CFSG.KC.BM.Twin.prod 4370 0 0 p106 v105
#kc_eval CFSG.KC.BM.FiveA p108 CFSG.KC.BM.Twin.prod 4370 0 0 p107 p107
#kc_eval CFSG.KC.BM.FiveA p109 CFSG.KC.BM.Twin.prod 4370 0 0 p108 p108
#kc_eval CFSG.KC.BM.FiveA p110 CFSG.KC.BM.Twin.prod 4370 0 0 p109 v105
#kc_eval CFSG.KC.BM.FiveA v111 CFSG.KC.BM.Twin.prod 4370 0 0 v102 p109
#kc_eval CFSG.KC.BM.FiveA v113 CFSG.KC.BM.Twin.prod 4370 0 0 p110 v101
