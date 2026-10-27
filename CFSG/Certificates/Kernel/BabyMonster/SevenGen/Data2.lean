module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Seven.Data0
import CFSG.Certificates.Kernel.BabyMonster.SevenGen.Data0
import CFSG.Certificates.Kernel.BabyMonster.SevenGen.Data1

#kc_eval CFSG.KC.BM.SevenGen r53 CFSG.KC.BM.Twin.prod 4370 2412240 5762301924005479200 x9 abi x9 CFSG.KC.BM.Seven.r0
#kc_eval CFSG.KC.BM.SevenGen r80 CFSG.KC.BM.Twin.prod 4370 2412240 240887046375700488 r53 r53
#kc_eval CFSG.KC.BM.SevenGen r81 CFSG.KC.BM.Twin.prod 4370 2412240 7121969007553006187 r80 r80
#kc_eval CFSG.KC.BM.SevenGen r54 CFSG.KC.BM.Twin.prod 4370 2412240 15089709175281803776 r53 r81
#kc_eval CFSG.KC.BM.SevenGen n2 CFSG.KC.BM.Twin.prod 4370 2412240 1451189820897259444 CFSG.KC.BM.Seven.r0 r54
#kc_eval CFSG.KC.BM.SevenGen n2i CFSG.KC.BM.Twin.inv 4370 2412240 3733660455526303315 n2
#kc_eval CFSG.KC.BM.SevenGen r96 CFSG.KC.BM.Twin.prod 4370 2412240 8140588714230742888 n2i n2i
#kc_eval CFSG.KC.BM.SevenGen r94 CFSG.KC.BM.Twin.prod 4370 2412240 17262227373794647544 n1 n2
#kc_eval CFSG.KC.BM.SevenGen r93 CFSG.KC.BM.Twin.prod 4370 2412240 5787605113511342374 n1 n2i
#kc_eval CFSG.KC.BM.SevenGen r98 CFSG.KC.BM.Twin.prod 4370 2412240 5565383632593566111 r94 r93
#kc_eval CFSG.KC.BM.SevenGen r95 CFSG.KC.BM.Twin.prod 4370 2412240 17624919699000584756 n2 n2
#kc_eval CFSG.KC.BM.SevenGen r99 CFSG.KC.BM.Twin.prod 4370 2412240 816899856775104171 r94 r95
