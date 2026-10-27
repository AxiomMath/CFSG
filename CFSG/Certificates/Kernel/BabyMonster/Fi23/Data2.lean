module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data0
import CFSG.Certificates.Kernel.BabyMonster.Five.Data0

#kc_eval CFSG.KC.BM.Fi23 r20 CFSG.KC.BM.Twin.prod 4370 2412240 14167023224937960939 CFSG.KC.BM.Five.f0 CFSG.KC.BM.Five.f2
#kc_eval CFSG.KC.BM.Fi23 r21 CFSG.KC.BM.Twin.prod 4370 2412240 11387873632816781491 CFSG.KC.BM.Five.f2 r20
#kc_eval CFSG.KC.BM.Fi23 r22 CFSG.KC.BM.Twin.prod 4370 2412240 9436571988541600944 r21 r21
#kc_eval CFSG.KC.BM.Fi23 ci23 CFSG.KC.BM.Twin.inv 4370 0 0 r22
#kc_eval CFSG.KC.BM.Fi23 U CFSG.KC.BM.Twin.prod 4370 2412240 4484684034817280270 ci23 r11 r22
