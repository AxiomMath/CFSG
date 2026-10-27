module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2Layer
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns

theorem i253_isComponentOf_of_layer {Q : Type*} [Group Q] {H J : Subgroup Q}
    (h : CFSG.Open.IsComponentOf J (GLALayer H)) : CFSG.Open.IsComponentOf J H :=
  ⟨h.1.trans (gfr2_layer_le H), isSubnormal_trans' h.2.1 (gfr2_layer_subnormal H), h.2.2⟩

end CFSG.HardMathSupport.Solomon.Coordinator
