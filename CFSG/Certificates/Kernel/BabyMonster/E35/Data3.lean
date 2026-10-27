module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.E35.Data1
import CFSG.Certificates.Kernel.BabyMonster.E35.Data2

#kc_eval CFSG.KC.BM.E35 wx CFSG.KC.BM.Twin.prod 4370 2412240 3739367729924924315 q ppq
#kc_eval CFSG.KC.BM.E35 wx2 CFSG.KC.BM.Twin.prod 4370 2412240 11463928451153779377 wx wx
#kc_eval CFSG.KC.BM.E35 wx3 CFSG.KC.BM.Twin.prod 4370 2412240 15933692341298641120 wx2 wx
#kc_eval CFSG.KC.BM.E35 x CFSG.KC.BM.Twin.prod 4370 2412240 12493284317006951554 wx3 wx3
#kc_eval CFSG.KC.BM.E35 x2 CFSG.KC.BM.Twin.prod 4370 2412240 41977616583305689 x x
#kc_eval CFSG.KC.BM.E35 x1 CFSG.KC.BM.Twin.prod 4370 2412240 8628025184425359144 gi x g
#kc_eval CFSG.KC.BM.E35 y2 CFSG.KC.BM.Twin.prod 4370 2412240 4731575311775851668 gi x1 g
