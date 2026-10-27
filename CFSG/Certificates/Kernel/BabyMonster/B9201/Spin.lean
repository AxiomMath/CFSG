module

import CFSG.Certificates.Kernel.Common.Eval
import CFSG.Certificates.Kernel.Common.LoadTree
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
meta import CFSG.Certificates.Kernel.BabyMonster.TwinSpin
import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0
import CFSG.Certificates.Kernel.BabyMonster.B9201.Data0
import CFSG.Certificates.Kernel.BabyMonster.B9201.Data2

#load_ktree CFSG.KC.BM.B9201.treeTxt "CFSG/Sporadic/Bridge/BTree.txt" 32768 1
#load_ktree CFSG.KC.BM.B9201.rowTxt "CFSG/Sporadic/Bridge/BRow0.txt" 2048 1
#kc_eval CFSG.KC.BM.B9201 u0 CFSG.KC.BM.Twin.rowText 4370 552 5385216556990640282 rowTxt.L0
#kc_eval CFSG.KC.BM.B9201 hinv CFSG.KC.BM.Twin.inv 4370 2412240 3987990155325425338 h
#kc_eval CFSG.KC.BM.B9201 bp CFSG.KC.BM.Twin.prod 4370 2412240 5281523701515176226 hinv r2 h
#kc_eval CFSG.KC.BM.B9201 Gp CFSG.KC.BM.Twin.intertw 4370 2412240 8510289506844013897 treeTxt.L0 1 CFSG.KC.BM.Seeds.A1 CFSG.KC.BM.Seeds.A2 u0 ap bp hinv
#kc_eval CFSG.KC.BM.B9201 Gip CFSG.KC.BM.Twin.inv 4370 2412240 15018819725167956111 Gp
#kc_eval CFSG.KC.BM.B9201 K CFSG.KC.BM.Twin.prod 4370 2412240 3663727545617136421 Gp h
