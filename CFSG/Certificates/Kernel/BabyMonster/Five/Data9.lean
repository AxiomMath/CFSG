module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Five.Data5
import CFSG.Certificates.Kernel.BabyMonster.Five.Data6
import CFSG.Certificates.Kernel.BabyMonster.Five.Data7
import CFSG.Certificates.Kernel.BabyMonster.Five.Data8

#kc_eval CFSG.KC.BM.Five f43 CFSG.KC.BM.Twin.prod 4370 2412240 14849240852189109051 f42 f38
#kc_eval CFSG.KC.BM.Five f44 CFSG.KC.BM.Twin.prod 4370 2412240 6349073582604386652 f43 f41
#kc_eval CFSG.KC.BM.Five f45 CFSG.KC.BM.Twin.prod 4370 2412240 12533079171894765117 f34 f44
#kc_eval CFSG.KC.BM.Five f56 CFSG.KC.BM.Twin.inv 4370 2412240 12139479789355192497 f44
#kc_eval CFSG.KC.BM.Five f46 CFSG.KC.BM.Twin.prod 4370 2412240 4377552935338954649 f45 f44
#kc_eval CFSG.KC.BM.Five f47 CFSG.KC.BM.Twin.prod 4370 2412240 3096738357665675903 f45 f46
#kc_eval CFSG.KC.BM.Five f48 CFSG.KC.BM.Twin.prod 4370 2412240 11317018101097261967 f45 f47
#kc_eval CFSG.KC.BM.Five f48_sq1 CFSG.KC.BM.Twin.prod 4370 2412240 10224329764904383359 f48 f48
#kc_eval CFSG.KC.BM.Five f48_sq2 CFSG.KC.BM.Twin.prod 4370 2412240 3817992229546679225 f48_sq1 f48_sq1
#kc_eval CFSG.KC.BM.Five f49 CFSG.KC.BM.Twin.prod 4370 2412240 11234265996007054689 f48_sq1 f48_sq2
#kc_eval CFSG.KC.BM.Five Z_sq1 CFSG.KC.BM.Twin.prod 4370 2412240 11234265996007054689 f49
#kc_eval CFSG.KC.BM.Five f51 CFSG.KC.BM.Twin.prod 4370 2412240 8699337482092042421 f49 f50
