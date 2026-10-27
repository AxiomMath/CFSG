module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data1
import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data3
import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data4

#kc_eval CFSG.KC.BM.Fi23 p4 CFSG.KC.BM.Twin.prod 4370 2412240 5703652903690986726 V g9 g5 g3 g3 g1
#kc_eval CFSG.KC.BM.Fi23 pi4 CFSG.KC.BM.Twin.inv 4370 0 0 p4
#kc_eval CFSG.KC.BM.Fi23 img4 CFSG.KC.BM.Twin.prod 4370 2412240 7779311762954739831 p4 D pi4
