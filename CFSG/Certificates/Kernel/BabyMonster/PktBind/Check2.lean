module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.PktCheck
public import CFSG.Certificates.Kernel.BabyMonster.PktSplit
public import CFSG.Certificates.Kernel.BabyMonster.PktBind.Check0
public import CFSG.Certificates.Kernel.BabyMonster.PktBind.Text
public import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Gens
public import CFSG.Certificates.Kernel.BabyMonster.Native.Small

set_option maxRecDepth 200000

#bm_bool CFSG.KD.PktBind sp24r (CFSG.KC.BM.Pkt.pktSparseRest (CFSG.KC.BM.Pkt.lineOf CH S 46) CFSG.KC.BM.Dyadic.SG24)
public theorem CFSG.KD.PktBind.sp24 :
    CFSG.KC.BM.Pkt.sparseOK (CFSG.KC.BM.Pkt.lineOf CFSG.KD.PktBind.CH CFSG.KD.PktBind.S (nat_lit 46))
      CFSG.KC.BM.Dyadic.SG24 = true :=
  CFSG.KC.BM.Pkt.pkt_sparseOK_of _ _ CFSG.KD.PktBind.ln46 CFSG.KD.PktBind.sp24r
#bm_bool CFSG.KD.PktBind sp25 (CFSG.KC.BM.Pkt.sparseOK (CFSG.KC.BM.Pkt.lineOf CH S 47) CFSG.KC.BM.Dyadic.SG25)
