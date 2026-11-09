module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
meta import CFSG.Certificates.Kernel.BabyMonster.TwinRank
import CFSG.Certificates.Kernel.BabyMonster.Five.Data18
import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data2
import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data9
import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data12

#kc_eval CFSG.KC.BM.FiveA p73 CFSG.KC.BM.Twin.prod 4370 0 0 v72 v72
#kc_eval CFSG.KC.BM.FiveA v77 CFSG.KC.BM.Twin.prod 4370 0 0 p73 v76
#kc_eval CFSG.KC.BM.FiveA p78 CFSG.KC.BM.Twin.prod 4370 0 0 v77 v77
#kc_eval CFSG.KC.BM.FiveA p79 CFSG.KC.BM.Twin.prod 4370 0 0 p78 v77
#kc_eval CFSG.KC.BM.FiveA p80 CFSG.KC.BM.Twin.prod 4370 0 0 p79 p79
#kc_eval CFSG.KC.BM.FiveA p81 CFSG.KC.BM.Twin.prod 4370 0 0 p80 v77
#kc_eval CFSG.KC.BM.FiveA p82 CFSG.KC.BM.Twin.prod 4370 0 0 p78 p78
#kc_eval CFSG.KC.BM.FiveA p83 CFSG.KC.BM.Twin.prod 4370 0 0 p82 p82
#kc_eval CFSG.KC.BM.FiveA v84 CFSG.KC.BM.Twin.prod 4370 0 0 v75 p81
#kc_eval CFSG.KC.BM.FiveA v85 CFSG.KC.BM.Twin.prod 4370 0 0 p83 v74
#kc_eval CFSG.KC.BM.FiveA v86 CFSG.KC.BM.Twin.prod 4370 0 0 v84 CFSG.KC.BM.Five.f85 v85
#kc_eval CFSG.KC.BM.FiveA p87 CFSG.KC.BM.Twin.prod 4370 0 0 v86 v86
#kc_eval CFSG.KC.BM.FiveA p88 CFSG.KC.BM.Twin.prod 4370 0 0 p87 p87
#kc_eval CFSG.KC.BM.FiveA p89 CFSG.KC.BM.Twin.prod 4370 0 0 p87 v86
#kc_eval CFSG.KC.BM.FiveA p90 CFSG.KC.BM.Twin.prod 4370 0 0 p67 p67
#kc_eval CFSG.KC.BM.FiveA p91 CFSG.KC.BM.Twin.prod 4370 0 0 p90 p67
#kc_eval CFSG.KC.BM.FiveA v92 CFSG.KC.BM.Twin.prod 4370 0 0 v86 p67 p88
#kc_eval CFSG.KC.BM.FiveA v93 CFSG.KC.BM.Twin.prod 4370 0 0 p91 v92
#kc_eval CFSG.KC.BM.FiveA v94 CFSG.KC.BM.Twin.prod 4370 0 0 v86 v93 p88
#kc_eval CFSG.KC.BM.FiveA v95a CFSG.KC.BM.Twin.prod 4370 0 0 p89 v93 p87
#kc_eval CFSG.KC.BM.FiveA v95 CFSG.KC.BM.Twin.prod 4370 0 0 v95a v94
#kc_eval CFSG.KC.BM.FiveA v96 CFSG.KC.BM.Twin.prod 4370 0 0 p67 v95
#kc_eval CFSG.KC.BM.FiveA v97 CFSG.KC.BM.Twin.prod 4370 0 0 v85 v96
#kc_eval CFSG.KC.BM.FiveA v177 CFSG.KC.BM.Twin.prod 4370 0 0 v97 v84
#kc_eval CFSG.KC.BM.FiveA c180 CFSG.KC.BM.Twin.prod 4370 0 0 v177 CFSG.KC.BM.Five.f85
#kc_eval CFSG.KC.BM.FiveA PrkW87 CFSG.KC.BM.Twin.rank 4370 0 0 v177 1 1
#kc_eval CFSG.KC.BM.FiveA RrkW87 CFSG.KC.BM.Twin.polyMul 4370 0 0 PrkW87 v177 1 1
