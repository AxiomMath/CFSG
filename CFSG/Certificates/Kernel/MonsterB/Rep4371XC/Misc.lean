module

public import Certificates.Data.Kernel.MonsterB.Rep4371XTau
public import Certificates.Data.Kernel.MonsterB.Rep4371XLab
public import Certificates.Data.Kernel.MonsterB.Rep4371XOct
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.BabyMonster.PktBind.Text
public import CFSG.Certificates.Kernel.MonsterB.Rep4371XC.LabText
import CFSG.Certificates.Kernel.BabyMonster.Load

set_option maxRecDepth 200000

#bm_bool CFSG.KC.Rep4371X.C tau (CFSG.KC.Rep4371X.tauLineChk (CFSG.KC.BM.Pkt.lineOf CFSG.KD.PktBind.CH CFSG.KD.PktBind.S 47))

#bm_bool CFSG.KC.Rep4371X.C lab (CFSG.KC.Rep4371X.labText CFSG.KD.KDF.TH (CFSG.KC.BM.Pkt.joinP CFSG.KD.PktLab.CH 0 151))

#bm_bool CFSG.KC.Rep4371X.C oct CFSG.KC.Rep4371X.octChk
