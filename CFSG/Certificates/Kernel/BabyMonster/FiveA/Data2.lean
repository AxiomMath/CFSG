module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data0
import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data1
import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0

#kc_eval CFSG.KC.BM.FiveA v12 CFSG.KC.BM.Twin.prod 4370 0 0 p6 CFSG.KC.BM.Seeds.A1 CFSG.KC.BM.Seeds.A2 CFSG.KC.BM.Seeds.A1 p6 CFSG.KC.BM.Seeds.A1
#kc_eval CFSG.KC.BM.FiveA v13 CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Seeds.A1 CFSG.KC.BM.Seeds.A2 CFSG.KC.BM.Seeds.A1 p6 CFSG.KC.BM.Seeds.A1 CFSG.KC.BM.Seeds.A2
#kc_eval CFSG.KC.BM.FiveA v14 CFSG.KC.BM.Twin.prod 4370 0 0 p11 v12 p11 v13
#kc_eval CFSG.KC.BM.FiveA p15 CFSG.KC.BM.Twin.prod 4370 0 0 v14 v14
