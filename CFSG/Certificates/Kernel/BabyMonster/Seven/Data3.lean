module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Seven.Data0
import CFSG.Certificates.Kernel.BabyMonster.Seven.Data1
import CFSG.Certificates.Kernel.BabyMonster.Seven.Data2

#kc_eval CFSG.KC.BM.Seven r41 CFSG.KC.BM.Twin.prod 4370 2412240 2690797747897198052 m1 m2i
#kc_eval CFSG.KC.BM.Seven r45 CFSG.KC.BM.Twin.prod 4370 2412240 7620928059534743416 r41 m2i
#kc_eval CFSG.KC.BM.Seven g CFSG.KC.BM.Twin.prod 4370 2412240 14290827896479055872 r46 m2 r45
#kc_eval CFSG.KC.BM.Seven r32 CFSG.KC.BM.Twin.prod 4370 2412240 8327351614877904897 g g
#kc_eval CFSG.KC.BM.Seven r33 CFSG.KC.BM.Twin.prod 4370 2412240 2593679180747285583 r32 r32
#kc_eval CFSG.KC.BM.Seven r34 CFSG.KC.BM.Twin.prod 4370 2412240 10784912729367443104 r33 r33
#kc_eval CFSG.KC.BM.Seven x CFSG.KC.BM.Twin.prod 4370 2412240 15611860709951440140 r32 r34
#kc_eval CFSG.KC.BM.Seven y CFSG.KC.BM.Twin.prod 4370 2412240 8774130754113525458 r33 x
#kc_eval CFSG.KC.BM.Seven w CFSG.KC.BM.Twin.prod 4370 2412240 4274095163342113213 r46 r45 r45 m2i m2i r42 r42
#kc_eval CFSG.KC.BM.Seven r35 CFSG.KC.BM.Twin.prod 4370 2412240 5240501614780475753 w w
#kc_eval CFSG.KC.BM.Seven r36 CFSG.KC.BM.Twin.prod 4370 2412240 8671639996489087963 r35 r35
#kc_eval CFSG.KC.BM.Seven r37 CFSG.KC.BM.Twin.prod 4370 2412240 7982388085011050986 r36 r36
