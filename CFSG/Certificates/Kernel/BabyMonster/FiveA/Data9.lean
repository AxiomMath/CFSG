module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data0
import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data1
import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data8
import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0

#kc_eval CFSG.KC.BM.FiveA v57 CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Seeds.A1 p6 CFSG.KC.BM.Seeds.A1 p6 CFSG.KC.BM.Seeds.A1 p6
#kc_eval CFSG.KC.BM.FiveA v58 CFSG.KC.BM.Twin.prod 4370 0 0 p11 v56 p11 v57
#kc_eval CFSG.KC.BM.FiveA p59 CFSG.KC.BM.Twin.prod 4370 0 0 v58 v58
#kc_eval CFSG.KC.BM.FiveA p60 CFSG.KC.BM.Twin.prod 4370 0 0 p59 v58
#kc_eval CFSG.KC.BM.FiveA p61 CFSG.KC.BM.Twin.prod 4370 0 0 p60 p60
#kc_eval CFSG.KC.BM.FiveA p62 CFSG.KC.BM.Twin.prod 4370 0 0 p61 p61
#kc_eval CFSG.KC.BM.FiveA v63 CFSG.KC.BM.Twin.prod 4370 0 0 v57 p62
#kc_eval CFSG.KC.BM.FiveA p64 CFSG.KC.BM.Twin.prod 4370 0 0 v63 v63
