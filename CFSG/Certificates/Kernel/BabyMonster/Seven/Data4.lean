module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Seven.Data0
import CFSG.Certificates.Kernel.BabyMonster.Seven.Data1
import CFSG.Certificates.Kernel.BabyMonster.Seven.Data3

#kc_eval CFSG.KC.BM.Seven h CFSG.KC.BM.Twin.prod 4370 2412240 6577136876967750631 r26 r41 r46 r41 r42 r45 r41 r41 m1
#kc_eval CFSG.KC.BM.Seven hi CFSG.KC.BM.Twin.inv 4370 2412240 14677238323714185946 h
#kc_eval CFSG.KC.BM.Seven y2 CFSG.KC.BM.Twin.prod 4370 2412240 6540750512683296151 y y
#kc_eval CFSG.KC.BM.Seven y3 CFSG.KC.BM.Twin.prod 4370 2412240 1317370198224907567 y y2
#kc_eval CFSG.KC.BM.Seven y4 CFSG.KC.BM.Twin.prod 4370 2412240 17322403730384822279 y2 y2
