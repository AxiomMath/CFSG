module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data0
import CFSG.Certificates.Kernel.BabyMonster.Five.Data0

#kc_eval CFSG.KC.BM.Fi23 r14 CFSG.KC.BM.Twin.prod 4370 2412240 9105424137904062472 r13 r13
#kc_eval CFSG.KC.BM.Fi23 r15 CFSG.KC.BM.Twin.prod 4370 2412240 3474355395068732113 CFSG.KC.BM.Five.f1 r14
#kc_eval CFSG.KC.BM.Fi23 ci16 CFSG.KC.BM.Twin.inv 4370 0 0 r15
#kc_eval CFSG.KC.BM.Fi23 V CFSG.KC.BM.Twin.prod 4370 2412240 1776828925862210936 ci16 r6 r15
