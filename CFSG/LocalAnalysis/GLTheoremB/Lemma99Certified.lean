module

public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Certified
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Proof

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open


theorem lemma99_of_inputs_certified (i20 : Input20_1) (i11 : Input11_6) (l23 : Lemma23)
    (i19 : Input19Delta) (i19' : Input19_1_6) (h95 : Prop95) (i113 : Input11_3)
    (i279 : Input27_9_3) : Lemma99 :=
  lemma99_of_inputs i20 i11 l23 i19 i19' CFSG.AGLEmbedding.kFactCatalogSchreier h95 i113 i279

theorem prop98_of_inputs_nine_certified (hS : Lemma911S) (i20 : Input20_1) (i11 : Input11_6)
    (l23 : Lemma23) (i19 : Input19Delta) (i19' : Input19_1_6) (h95 : Prop95) (i113 : Input11_3)
    (i279 : Input27_9_3) (i22 : Input22_5) (iPi : InputPiGen) : Prop98 :=
  prop98_of_inputs_S_certified hS i20 i11 l23 i19 i19' (prop95Core_of_prop95 h95)
    (lemma99_of_inputs_certified i20 i11 l23 i19 i19' h95 i113 i279) i22 iPi

end CFSG.LocalAnalysis.GLTheoremB
