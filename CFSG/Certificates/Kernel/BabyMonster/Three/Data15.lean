module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Three.Data11
import CFSG.Certificates.Kernel.BabyMonster.Three.Data12
import CFSG.Certificates.Kernel.BabyMonster.Three.Data14

#kc_eval CFSG.KC.BM.Three t74 CFSG.KC.BM.Twin.inv 4370 2412240 16463832759468277680 t73
#kc_eval CFSG.KC.BM.Three t76 CFSG.KC.BM.Twin.prod 4370 2412240 14895509010999516888 t74 t66
#kc_eval CFSG.KC.BM.Three t77 CFSG.KC.BM.Twin.prod 4370 2412240 2411116789839439906 t75 t76
#kc_eval CFSG.KC.BM.Three t78 CFSG.KC.BM.Twin.prod 4370 2412240 14004056212882880943 t77 t73
#kc_eval CFSG.KC.BM.Three t79 CFSG.KC.BM.Twin.prod 4370 2412240 6467888348371362928 t53 t78
#kc_eval CFSG.KC.BM.Three t79_sq1 CFSG.KC.BM.Twin.prod 4370 2412240 7521213743418286642 t79 t79
#kc_eval CFSG.KC.BM.Three t79_inv CFSG.KC.BM.Twin.inv 4370 0 0 t79
#kc_eval CFSG.KC.BM.Three ox_pp0 CFSG.KC.BM.Twin.prod 4370 2412240 2335554017543818023 t79 t79_sq1
#kc_eval CFSG.KC.BM.Three t79_sq2 CFSG.KC.BM.Twin.prod 4370 2412240 3657910366082588540 t79_sq1 t79_sq1
