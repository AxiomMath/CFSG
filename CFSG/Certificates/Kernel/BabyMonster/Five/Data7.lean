module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Five.Data5

#kc_eval CFSG.KC.BM.Five f33_sq1 CFSG.KC.BM.Twin.prod 4370 2412240 1952671890762295294 f33 f33
#kc_eval CFSG.KC.BM.Five f33_sq2 CFSG.KC.BM.Twin.prod 4370 2412240 14938550817139795976 f33_sq1 f33_sq1
#kc_eval CFSG.KC.BM.Five f33_sq3 CFSG.KC.BM.Twin.prod 4370 2412240 11076878974468290194 f33_sq2 f33_sq2
#kc_eval CFSG.KC.BM.Five f33_sq4 CFSG.KC.BM.Twin.prod 4370 2412240 6020077387894784917 f33_sq3 f33_sq3
#kc_eval CFSG.KC.BM.Five f39 CFSG.KC.BM.Twin.prod 4370 2412240 13426030930841297591 f33_sq2 f33_sq4
#kc_eval CFSG.KC.BM.Five f41 CFSG.KC.BM.Twin.prod 4370 2412240 3599636613963353641 f39 f40
#kc_eval CFSG.KC.BM.Five f42 CFSG.KC.BM.Twin.inv 4370 2412240 16986242281496151813 f41
