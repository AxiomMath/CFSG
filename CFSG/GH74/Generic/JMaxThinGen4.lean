module

public import CFSG.GH74.Generic.JMaxThin
public import CFSG.GH74.GLS.AssemblyBridge

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.Blueprint

@[expose] def S_corTwoThinGen4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], GLS.IsKProperSimple G → Gen4 G → KGH G →
    (∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G)) → 3 ≤ Open.twoRank G →
      GLS.L2Meets G GLS.InG2 → ¬ GLS.HasTwoThinConfiguration G

theorem s_genericThin_of_corTwoThinGen4 (h : S_corTwoThinGen4) : S_genericThin :=
  fun G _ _ hs hn hr hgen hK hnab _ hg hthin =>
    (h G (GLS.isKProperSimple_of_kgh hs hn hK) hgen hK hnab hr hg hthin).elim

end CFSG.GH74.Generic
