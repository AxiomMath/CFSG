module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.PktCheck
public import CFSG.Certificates.Kernel.BabyMonster.PktBind.Text
public import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Gens
public import CFSG.Certificates.Kernel.BabyMonster.Native.Small

set_option maxRecDepth 200000

#bm_bool CFSG.KD.PktBind sp24 (CFSG.KC.BM.Pkt.sparseOK (CFSG.KC.BM.Pkt.lineOf CH S 46) CFSG.KC.BM.Dyadic.SG24)
#bm_bool CFSG.KD.PktBind sp25 (CFSG.KC.BM.Pkt.sparseOK (CFSG.KC.BM.Pkt.lineOf CH S 47) CFSG.KC.BM.Dyadic.SG25)
