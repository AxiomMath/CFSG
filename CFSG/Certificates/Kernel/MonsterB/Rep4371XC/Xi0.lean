module

public import Certificates.Data.Kernel.MonsterB.Rep4371XGen
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.BabyMonster.PktBind.Text
import CFSG.Certificates.Kernel.BabyMonster.Load
import CFSG.Certificates.Kernel.BabyMonster.LoadRange

set_option maxRecDepth 200000

#bm_bool CFSG.KC.Rep4371X.C xiLen (CFSG.KC.Rep4371X.xiLenChk CFSG.KD.PktBind.CH CFSG.KD.PktBind.S)

#bm_range CFSG.KC.Rep4371X.C xi 0 5 (CFSG.KC.Rep4371X.xiChk CFSG.KD.KDF.TH CFSG.KD.PktBind.CH CFSG.KD.PktBind.S)
