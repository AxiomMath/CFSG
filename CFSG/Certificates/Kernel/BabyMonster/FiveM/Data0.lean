module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Max15.Data0
import CFSG.Certificates.Kernel.BabyMonster.Max15.Data4

#kc_eval CFSG.KC.BM.FiveM q4 CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Max15.r16 CFSG.KC.BM.Max15.r16
#kc_eval CFSG.KC.BM.FiveM q8 CFSG.KC.BM.Twin.prod 4370 0 0 q4 q4
#kc_eval CFSG.KC.BM.FiveM q12 CFSG.KC.BM.Twin.prod 4370 0 0 q8 q4
#kc_eval CFSG.KC.BM.FiveM s CFSG.KC.BM.Twin.prod 4370 0 0 q12 CFSG.KC.BM.Max15.r16
#kc_eval CFSG.KC.BM.FiveM y CFSG.KC.BM.Twin.prod 4370 0 0 s CFSG.KC.BM.Max15.g2
#kc_eval CFSG.KC.BM.FiveM s2 CFSG.KC.BM.Twin.prod 4370 0 0 s s
#kc_eval CFSG.KC.BM.FiveM s4 CFSG.KC.BM.Twin.prod 4370 0 0 s2 s2
#kc_eval CFSG.KC.BM.FiveM g1c CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Max15.g1 CFSG.KC.BM.Max15.g1 CFSG.KC.BM.Max15.g1
#kc_eval CFSG.KC.BM.FiveM y1 CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Max15.g1 y g1c
#kc_eval CFSG.KC.BM.FiveM w CFSG.KC.BM.Twin.prod 4370 0 0 y1 y
#kc_eval CFSG.KC.BM.FiveM w2 CFSG.KC.BM.Twin.prod 4370 0 0 w w
#kc_eval CFSG.KC.BM.FiveM w4 CFSG.KC.BM.Twin.prod 4370 0 0 w2 w2
#kc_eval CFSG.KC.BM.FiveM a CFSG.KC.BM.Twin.prod 4370 0 0 w4 w
#kc_eval CFSG.KC.BM.FiveM v CFSG.KC.BM.Twin.prod 4370 0 0 y y1
#kc_eval CFSG.KC.BM.FiveM v2 CFSG.KC.BM.Twin.prod 4370 0 0 v v
#kc_eval CFSG.KC.BM.FiveM v4 CFSG.KC.BM.Twin.prod 4370 0 0 v2 v2
#kc_eval CFSG.KC.BM.FiveM b CFSG.KC.BM.Twin.prod 4370 0 0 v4 v
#kc_eval CFSG.KC.BM.FiveM ab CFSG.KC.BM.Twin.prod 4370 0 0 a b
#kc_eval CFSG.KC.BM.FiveM aS CFSG.KC.BM.Twin.prod 4370 0 0 a s
