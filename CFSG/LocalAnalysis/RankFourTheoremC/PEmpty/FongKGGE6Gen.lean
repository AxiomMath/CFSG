module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGGE6Defs
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.IrrationalRoot
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergRoot
public import CFSG.RankThree.PartOne.CTP.SeitzMaxSLRoot
public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon

public noncomputable section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGG

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.E6Pilot
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
open scoped Pointwise

set_option linter.unusedSectionVars false


theorem kgg_card_eq_card_fix_sq {F : Type} [Field F] [Finite F] [CharP F 2] {δ : F ≃+* F}
    (hδ2 : δ * δ = 1) (hδ1 : δ ≠ 1) :
    Nat.card F = Nat.card (CFSG.LieType.Chevalley.fixSubfield δ) ^ 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  have hF : Nat.card F = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hord : orderOf δ = 2 := orderOf_eq_prime (show δ ^ 2 = 1 by rw [sq]; exact hδ2) hδ1
  obtain ⟨hdvd, hcard⟩ :=
    CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two n.pos hF δ
  rw [hord] at hdvd hcard
  obtain ⟨m, hm⟩ := hdvd
  rw [hF, hcard, hm, Nat.mul_div_cancel_left m (by norm_num : 0 < 2)]
  ring

theorem e6_gen_core {F : Type} [Field F] [Finite F] [CharP F 2] {δ : F ≃+* F}
    (hδ2 : δ * δ = 1) (hδ1 : δ ≠ 1) {τ : MulAut (C6 F)}
    (hτ : ∀ c : F, τ (xPar (rootOperatorFamily Tag.E6) e6HighestRoot c) =
      xPar (rootOperatorFamily Tag.E6) e6HighestRoot c) :
    Subgroup.closure ({x : C6 F | entrywiseAdjointAut Tag.E6 δ x = x} ∪
      {x : C6 F | τ x = x}) = ⊤ := by
  have hK : Nat.card F = Nat.card (CFSG.LieType.Chevalley.fixSubfield δ) ^ 2 :=
    kgg_card_eq_card_fix_sq hδ2 hδ1
  have hk : ∀ S : Subfield F, CFSG.LieType.Chevalley.fixSubfield δ ≤ S →
      S = CFSG.LieType.Chevalley.fixSubfield δ ∨ S = ⊤ := fun S hS =>
    CFSG.RankThree.PartOne.CTP.subfield_eq_or_eq_top hS Nat.prime_two hK
  obtain ⟨t, ht⟩ : ∃ t : F, δ t ≠ t := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hδ1 (RingEquiv.ext fun x => h x)
  have ht' : t ∉ CFSG.LieType.Chevalley.fixSubfield δ := fun h =>
    ht ((CFSG.LieType.Chevalley.mem_fixSubfield δ).mp h)
  refine CFSG.LieType.SeitzGeneration.ExcOuterLeOne.eq_top_of_irrational_rootElt
    (τ := Tag.E6) (Or.inl rfl) (CFSG.LieType.Chevalley.fixSubfield δ) hk _ ?_ e6HighestRoot
    isRoot_e6HighestRoot t ht' ?_
  ·
    intro γ _ c hc
    refine Subgroup.subset_closure (Set.mem_union_left _ ?_)
    show entrywiseAdjointAut Tag.E6 δ (xPar (rootOperatorFamily Tag.E6) γ c) =
      xPar (rootOperatorFamily Tag.E6) γ c
    rw [CFSG.StandardType.AutSt.entrywiseAdjointAut_xPar,
      (CFSG.LieType.Chevalley.mem_fixSubfield δ).mp hc]
  ·
    exact Subgroup.subset_closure (Set.mem_union_right _ (hτ t))

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGG
