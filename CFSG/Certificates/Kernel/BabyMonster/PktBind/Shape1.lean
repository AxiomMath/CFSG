module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import Certificates.Data.Kernel.BabyMonster.PktShape
public import CFSG.Certificates.Kernel.BabyMonster.PktBind.Text
public import CFSG.Certificates.Kernel.BabyMonster.PktSplit

set_option maxRecDepth 200000

#bm_bool CFSG.KD.PktBind shape24 (CFSG.KC.BM.Pkt.shapeOK (CFSG.KC.BM.Pkt.lineOf CH S 24))
#bm_bool CFSG.KD.PktBind shape25 (CFSG.KC.BM.Pkt.shapeOK (CFSG.KC.BM.Pkt.lineOf CH S 25))
#bm_bool CFSG.KD.PktBind shape26 (CFSG.KC.BM.Pkt.shapeOK (CFSG.KC.BM.Pkt.lineOf CH S 26))
#bm_bool CFSG.KD.PktBind shape27 (CFSG.KC.BM.Pkt.shapeOK (CFSG.KC.BM.Pkt.lineOf CH S 27))
#bm_bool CFSG.KD.PktBind shape28 (CFSG.KC.BM.Pkt.shapeOK (CFSG.KC.BM.Pkt.lineOf CH S 28))
#bm_bool CFSG.KD.PktBind shape29 (CFSG.KC.BM.Pkt.shapeOK (CFSG.KC.BM.Pkt.lineOf CH S 29))
#bm_bool CFSG.KD.PktBind shape30 (CFSG.KC.BM.Pkt.shapeOK (CFSG.KC.BM.Pkt.lineOf CH S 30))
#bm_bool CFSG.KD.PktBind shape31 (CFSG.KC.BM.Pkt.shapeOK (CFSG.KC.BM.Pkt.lineOf CH S 31))
#bm_bool CFSG.KD.PktBind shape32 (CFSG.KC.BM.Pkt.shapeOK (CFSG.KC.BM.Pkt.lineOf CH S 32))
#bm_bool CFSG.KD.PktBind shape33 (CFSG.KC.BM.Pkt.shapeOK (CFSG.KC.BM.Pkt.lineOf CH S 33))
#bm_bool CFSG.KD.PktBind shape34 (CFSG.KC.BM.Pkt.shapeOK (CFSG.KC.BM.Pkt.lineOf CH S 34))
#bm_bool CFSG.KD.PktBind shape35 (CFSG.KC.BM.Pkt.shapeOK (CFSG.KC.BM.Pkt.lineOf CH S 35))
#bm_bool CFSG.KD.PktBind shape36 (CFSG.KC.BM.Pkt.shapeOK (CFSG.KC.BM.Pkt.lineOf CH S 36))
#bm_bool CFSG.KD.PktBind shape37 (CFSG.KC.BM.Pkt.shapeOK (CFSG.KC.BM.Pkt.lineOf CH S 37))
#bm_bool CFSG.KD.PktBind shape38 (CFSG.KC.BM.Pkt.shapeOK (CFSG.KC.BM.Pkt.lineOf CH S 38))
#bm_bool CFSG.KD.PktBind shape39 (CFSG.KC.BM.Pkt.shapeOK (CFSG.KC.BM.Pkt.lineOf CH S 39))
#bm_bool CFSG.KD.PktBind shape40 (CFSG.KC.BM.Pkt.shapeOK (CFSG.KC.BM.Pkt.lineOf CH S 40))
#bm_bool CFSG.KD.PktBind shape41 (CFSG.KC.BM.Pkt.shapeOK (CFSG.KC.BM.Pkt.lineOf CH S 41))
#bm_bool CFSG.KD.PktBind shape42 (CFSG.KC.BM.Pkt.shapeOK (CFSG.KC.BM.Pkt.lineOf CH S 42))
#bm_bool CFSG.KD.PktBind shape43 (CFSG.KC.BM.Pkt.shapeOK (CFSG.KC.BM.Pkt.lineOf CH S 43))
#bm_bool CFSG.KD.PktBind shape44 (CFSG.KC.BM.Pkt.shapeOK (CFSG.KC.BM.Pkt.lineOf CH S 44))
#bm_bool CFSG.KD.PktBind shape45 (CFSG.KC.BM.Pkt.shapeOK (CFSG.KC.BM.Pkt.lineOf CH S 45))
@[expose] public noncomputable def CFSG.KD.PktBind.shape46s1 : Nat × Nat × Bool := (nat_lit 2576, nat_lit 2578, true)
@[expose] public noncomputable def CFSG.KD.PktBind.shape46s2 : Nat × Nat × Bool := (nat_lit 3102, nat_lit 4122, true)
#bm_bool CFSG.KD.PktBind shape46a (CFSG.KC.BM.Pkt.pktShapeHead (CFSG.KC.BM.Pkt.lineOf CH S 46) 6451 shape46s1)
#bm_bool CFSG.KD.PktBind shape46b (CFSG.KC.BM.Pkt.pktShapeMid (CFSG.KC.BM.Pkt.lineOf CH S 46) 6451 14859 shape46s1 shape46s2)
#bm_bool CFSG.KD.PktBind shape46c (CFSG.KC.BM.Pkt.pktShapeTail (CFSG.KC.BM.Pkt.lineOf CH S 46) 14859 shape46s2)
public theorem CFSG.KD.PktBind.shape46 :
    CFSG.KC.BM.Pkt.shapeOK (CFSG.KC.BM.Pkt.lineOf CFSG.KD.PktBind.CH CFSG.KD.PktBind.S (nat_lit 46)) =
      true :=
  CFSG.KC.BM.Pkt.pkt_shapeOK_split3 _ (nat_lit 6451) (nat_lit 14859) (by decide) _ _
    CFSG.KD.PktBind.shape46a CFSG.KD.PktBind.shape46b CFSG.KD.PktBind.shape46c
#bm_bool CFSG.KD.PktBind shape47 (CFSG.KC.BM.Pkt.shapeOK (CFSG.KC.BM.Pkt.lineOf CH S 47))
