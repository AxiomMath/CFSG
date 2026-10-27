module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.Close
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6M10

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup

theorem card_M10 : Nat.card M10 = 720 := by
  obtain ⟨e⟩ := CFSG.QuasithinUnique.Unc25G2.nonempty_stabilizer_zero_equiv_m10
  have h1 : 720 ≤ Nat.card M10 := by
    have := CFSG.QuasithinUnique.Unc25G2.card_m10_ge
    rwa [← Nat.card_congr e.toEquiv] at this
  have h2 : Nat.card M10 ≤ 720 := by
    have hle : CFSG.Sporadic.Bridge.M11.stab1 ≤ CFSG.Blueprint.NativeSporadic.M11 :=
      fun g hg => hg.1
    have h3 : Nat.card M10 = Nat.card CFSG.Sporadic.Bridge.M11.stab1 := by
      change Nat.card (MulAction.stabilizer ↥CFSG.Blueprint.NativeSporadic.M11 (0 : Fin 11)) = _
      rw [CFSG.QuasithinUnique.Unc25G2.stabilizer_zero_eq_subgroupOf]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    rw [h3]
    exact (CFSG.QuasithinUnique.Unc25G2.m11_stab_card_le).1
  omega

theorem closing_abstract_cert
    (hGH1 : GHLemma53_1)
    (hOut : OutU43TwoGroup) {X : Type} [Group X] [Finite X]
    (hKX : CFSG.SectionRank.IsKGroupCat X) (d : ThreeLocalData X) : False :=
  closing_abstract hGH1 hOut card_M10 hKX d

end CFSG.EvenSporadicStandard.RuStd.S2
