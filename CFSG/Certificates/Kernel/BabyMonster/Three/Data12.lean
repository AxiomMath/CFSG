module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Three.Data5
import CFSG.Certificates.Kernel.BabyMonster.Three.Data8
import CFSG.Certificates.Kernel.BabyMonster.Three.Data11

#kc_eval CFSG.KC.BM.Three t50 CFSG.KC.BM.Twin.prod 4370 2412240 7395322165144287118 Zp2
#kc_eval CFSG.KC.BM.Three t51 CFSG.KC.BM.Twin.prod 4370 2412240 5976228940005337120 t50 t38
#kc_eval CFSG.KC.BM.Three t56 CFSG.KC.BM.Twin.prod 4370 2412240 13109800147703149187 t50 t45
#kc_eval CFSG.KC.BM.Three t53 CFSG.KC.BM.Twin.prod 4370 2412240 7835775889307353057 t52 t51
#kc_eval CFSG.KC.BM.Three t58 CFSG.KC.BM.Twin.prod 4370 2412240 12198696740191948096 t57 t56
#kc_eval CFSG.KC.BM.Three t58_sq1 CFSG.KC.BM.Twin.prod 4370 2412240 8375714326817864434 t58 t58
#kc_eval CFSG.KC.BM.Three t58_inv CFSG.KC.BM.Twin.inv 4370 0 0 t58
#kc_eval CFSG.KC.BM.Three oh_pp0 CFSG.KC.BM.Twin.prod 4370 2412240 17379729094248342741 t58 t58_sq1
#kc_eval CFSG.KC.BM.Three t58_sq2 CFSG.KC.BM.Twin.prod 4370 2412240 11498851981887967228 t58_sq1 t58_sq1
