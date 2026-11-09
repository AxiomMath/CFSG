module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0

#kc_eval CFSG.KC.BM.FiveA p6 CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Seeds.A2 CFSG.KC.BM.Seeds.A2
#kc_eval CFSG.KC.BM.FiveA v12a CFSG.KC.BM.Twin.prod 4370 0 0 p6 CFSG.KC.BM.Seeds.A1 CFSG.KC.BM.Seeds.A2
#kc_eval CFSG.KC.BM.FiveA v13a CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Seeds.A1 CFSG.KC.BM.Seeds.A2 CFSG.KC.BM.Seeds.A1
#kc_eval CFSG.KC.BM.FiveA v57a CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Seeds.A1 p6 CFSG.KC.BM.Seeds.A1
#kc_eval CFSG.KC.BM.FiveA v12 CFSG.KC.BM.Twin.prod 4370 0 0 v12a v57a
#kc_eval CFSG.KC.BM.FiveA v13 CFSG.KC.BM.Twin.prod 4370 0 0 v13a v12a
#kc_eval CFSG.KC.BM.FiveA v44a CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Seeds.A1 p6 CFSG.KC.BM.Seeds.A1
#kc_eval CFSG.KC.BM.FiveA v44b CFSG.KC.BM.Twin.prod 4370 0 0 v44a p6 CFSG.KC.BM.Seeds.A1
#kc_eval CFSG.KC.BM.FiveA v44c CFSG.KC.BM.Twin.prod 4370 0 0 v44b CFSG.KC.BM.Seeds.A2 CFSG.KC.BM.Seeds.A1
#kc_eval CFSG.KC.BM.FiveA v44d CFSG.KC.BM.Twin.prod 4370 0 0 v44c CFSG.KC.BM.Seeds.A2 CFSG.KC.BM.Seeds.A1
#kc_eval CFSG.KC.BM.FiveA v44 CFSG.KC.BM.Twin.prod 4370 0 0 v44d p6
#kc_eval CFSG.KC.BM.FiveA v45a CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Seeds.A2 CFSG.KC.BM.Seeds.A1 p6
#kc_eval CFSG.KC.BM.FiveA v45b CFSG.KC.BM.Twin.prod 4370 0 0 v45a CFSG.KC.BM.Seeds.A1 p6
#kc_eval CFSG.KC.BM.FiveA v45c CFSG.KC.BM.Twin.prod 4370 0 0 v45b CFSG.KC.BM.Seeds.A1 CFSG.KC.BM.Seeds.A2
#kc_eval CFSG.KC.BM.FiveA v45d CFSG.KC.BM.Twin.prod 4370 0 0 v45c CFSG.KC.BM.Seeds.A1 CFSG.KC.BM.Seeds.A2
#kc_eval CFSG.KC.BM.FiveA v45 CFSG.KC.BM.Twin.prod 4370 0 0 v45d CFSG.KC.BM.Seeds.A1
#kc_eval CFSG.KC.BM.FiveA v74a CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Seeds.A2 CFSG.KC.BM.Seeds.A1 p6
#kc_eval CFSG.KC.BM.FiveA v74 CFSG.KC.BM.Twin.prod 4370 0 0 v74a CFSG.KC.BM.Seeds.A1
#kc_eval CFSG.KC.BM.FiveA v75 CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Seeds.A1 CFSG.KC.BM.Seeds.A2 CFSG.KC.BM.Seeds.A1 p6
#kc_eval CFSG.KC.BM.FiveA v101 CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Seeds.A2 CFSG.KC.BM.Seeds.A1 CFSG.KC.BM.Seeds.A2
#kc_eval CFSG.KC.BM.FiveA v102 CFSG.KC.BM.Twin.prod 4370 0 0 p6 CFSG.KC.BM.Seeds.A1 p6
#kc_eval CFSG.KC.BM.FiveA v56 CFSG.KC.BM.Twin.prod 4370 0 0 v101 v13a
#kc_eval CFSG.KC.BM.FiveA v57 CFSG.KC.BM.Twin.prod 4370 0 0 v57a v102
#kc_eval CFSG.KC.BM.FiveA v147 CFSG.KC.BM.Twin.prod 4370 0 0 v75 v13a
#kc_eval CFSG.KC.BM.FiveA v148 CFSG.KC.BM.Twin.prod 4370 0 0 v57a v74
