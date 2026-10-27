module

import CFSG.Certificates.Kernel.Common.Eval
import CFSG.Certificates.Kernel.Common.LoadTree
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
meta import CFSG.Certificates.Kernel.BabyMonster.TwinSpin
import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0
import CFSG.Certificates.Kernel.BabyMonster.TcFive.Data5

#load_ktree CFSG.KC.BM.TcFive.treeTxt "CFSG/Sporadic/Bridge/BTree.txt" 32768 1
#load_ktree CFSG.KC.BM.TcFive.rowTxt "CFSG/Sporadic/Bridge/BTcRow.txt" 2048 1
#kc_eval CFSG.KC.BM.TcFive u0 CFSG.KC.BM.Twin.rowText 4370 0 0 rowTxt.L0
#kc_eval CFSG.KC.BM.TcFive G CFSG.KC.BM.Twin.intertw 4370 0 0 treeTxt.L0 1 CFSG.KC.BM.Seeds.A1 CFSG.KC.BM.Seeds.A2 u0 AP BP
#kc_eval CFSG.KC.BM.TcFive Gi CFSG.KC.BM.Twin.inv 4370 0 0 G
