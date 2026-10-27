module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Reduction
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.FactsConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Spine

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSmallLie

theorem Std.of_hyp
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hL : StdHyp G L)
    (hc : Nat.card (center L) = 2) (hq : IsSporadic (L ⧸ center L) .Fi22) {t : G}
    (ht : (center L).map L.subtype = zpowers t)
    (hr : L.relIndex (centralizer ({t} : Set G)) = 2) {E : Subgroup G} (hE : E ≤ L)
    (hM : M24Out G E t) : Std G L E t := by
  have hsimple := hL.simple
  have ht2 : orderOf t = 2 := orderOf_eq_two_of_center hc ht
  have htZ : t ∈ (center L).map L.subtype := ht ▸ mem_zpowers t
  obtain ⟨htC, hCc, hC2, -, -, -, -⟩ := std_center_facts hL.toStandardSetting ht2 htZ
  obtain ⟨E', M⟩ := exists_localModel (fi22CoverRest_of_aut fi22CoverAut) hL.standard.1 hc hq
  have hout := relIndex_sup_centralizer_le_two hL hq htC ht2
  have D : Facts G t L E :=
    (Facts.of_localModel hL ht2 htZ M hout).of_elementary hE hM.E_sq hM.card_E
  refine ⟨hL, hc, hq, ht, ?_, hE, D, ?_, hM⟩
  · intro heq
    rw [heq, Subgroup.relIndex_self] at hr
    exact absurd hr (by norm_num)
  · refine D.centralizer_eq_zpowers hL.nonabelian ht2 hCc hC2 htC ?_
    rw [hM.centralizer_eq]
    exact le_sup_left

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
