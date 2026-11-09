module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
meta import CFSG.Certificates.Kernel.BabyMonster.TwinRank
import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data0
import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data3
import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data15

#kc_eval CFSG.KC.BM.FiveA v31 CFSG.KC.BM.Twin.prod 4370 0 0 v27 p26 p29
#kc_eval CFSG.KC.BM.FiveA v32 CFSG.KC.BM.Twin.prod 4370 0 0 p26 v31
#kc_eval CFSG.KC.BM.FiveA v33 CFSG.KC.BM.Twin.prod 4370 0 0 v27 v32 p29
#kc_eval CFSG.KC.BM.FiveA v34 CFSG.KC.BM.Twin.prod 4370 0 0 p30 v32 p28 v33
#kc_eval CFSG.KC.BM.FiveA v35 CFSG.KC.BM.Twin.prod 4370 0 0 p26 v34
#kc_eval CFSG.KC.BM.FiveA v36 CFSG.KC.BM.Twin.prod 4370 0 0 v27 v35 p29
#kc_eval CFSG.KC.BM.FiveA v37 CFSG.KC.BM.Twin.prod 4370 0 0 v35 v36
#kc_eval CFSG.KC.BM.FiveA v38 CFSG.KC.BM.Twin.prod 4370 0 0 v27 v37 p29
#kc_eval CFSG.KC.BM.FiveA v39 CFSG.KC.BM.Twin.prod 4370 0 0 p30 v37 p28 v38
#kc_eval CFSG.KC.BM.FiveA v40 CFSG.KC.BM.Twin.prod 4370 0 0 v35 v39
#kc_eval CFSG.KC.BM.FiveA c41 CFSG.KC.BM.Twin.prod 4370 0 0 v40 v27
#kc_eval CFSG.KC.BM.FiveA PrkYA CFSG.KC.BM.Twin.rank 4370 0 0 b4 1 1
#kc_eval CFSG.KC.BM.FiveA RrkYA CFSG.KC.BM.Twin.polyMul 4370 0 0 PrkYA b4 1 1
#kc_eval CFSG.KC.BM.FiveA PrkW48 CFSG.KC.BM.Twin.rank 4370 0 0 v40 1 1
#kc_eval CFSG.KC.BM.FiveA RrkW48 CFSG.KC.BM.Twin.polyMul 4370 0 0 PrkW48 v40 1 1
