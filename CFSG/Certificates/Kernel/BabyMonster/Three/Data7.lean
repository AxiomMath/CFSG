module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Three.Data4

#kc_eval CFSG.KC.BM.Three t36 CFSG.KC.BM.Twin.prod 4370 2412240 7047479160198220479 t30 t35
#kc_eval CFSG.KC.BM.Three t36_sq1 CFSG.KC.BM.Twin.prod 4370 2412240 17574751424148313007 t36 t36
#kc_eval CFSG.KC.BM.Three t36_sq2 CFSG.KC.BM.Twin.prod 4370 2412240 3331241557929490462 t36_sq1 t36_sq1
#kc_eval CFSG.KC.BM.Three t36_sq3 CFSG.KC.BM.Twin.prod 4370 2412240 14926586588952460117 t36_sq2 t36_sq2
#kc_eval CFSG.KC.BM.Three t36_sq4 CFSG.KC.BM.Twin.prod 4370 2412240 6632851038903567689 t36_sq3 t36_sq3
#kc_eval CFSG.KC.BM.Three t41 CFSG.KC.BM.Twin.prod 4370 2412240 3686194589356962763 t36_sq3 t36_sq4
