module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3AGap
public import CFSG.Quasithin.Background.A318PL3Lin

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Solomon.LocalBalance

theorem descend_eq_one_of_inndiag_field_model {Y M : Type*} [Group Y] [Group M]
    (e : (Y ⧸ Subgroup.center Y) ≃* M) (P : PinnedAut M) (hP : GoodPinned P) {α : MulAut Y}
    (h : MulAut.congr e (centerDescend Y α) ∈ P.inndiag) (hf : IsFieldAutThree α) :
    centerDescend Y α = 1 := by
  rcases hf with h1 | hL | hU
  · rw [h1, map_one]
  · obtain ⟨F, _, _, e', σ, γ, he⟩ := fieldAutPSL3_data hL
    exact eq_one_of_inndiag_of_field hP (goodPinned_psl F) e e' h
      (show fieldAut 3 F σ ∈ (stdPinnedPSL 3 F).field from ⟨σ, rfl⟩) γ he
  · obtain ⟨p, f, F, _, hF, e', σ, γ, hodd, he⟩ := fieldAutPSU3_data hU
    by_cases hq : 2 < p ^ f
    · exact eq_one_of_inndiag_of_field hP (goodPinned_psu hF hq) e e' h
        (show psuField hF σ ∈ (stdPinnedPSU3 hF).field from ⟨σ, rfl⟩) γ he
    · have hfin := hF.finite
      have h2 : p ^ f = 2 := pow_eq_two_of_not_two_lt hF hq
      have hcard : Nat.card F = 2 ^ 2 := by rw [hF.card, pow_mul', h2]
      have hσ := eq_one_of_odd_orderOf_card_four hcard hodd
      rw [hσ, map_one, mul_one, mul_inv_cancel] at he
      exact (MulAut.congr e').injective (by rw [he, map_one])

theorem exists_autModel {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    {ε : MulAut Y} (hε : IsFieldAutPSL3 ε ∨ IsFieldAutPSU3 ε) :
    ∃ (M : Type) (_ : Group M) (e : (Y ⧸ Subgroup.center Y) ≃* M) (P : PinnedAut M)
      (_ : GoodPinned P) (C : Type) (_ : Group C) (_ : IsCyclic C) (fld : C →* MulAut M),
      (∀ (β : MulAut M) (k : ℕ), orderOf β = 3 ^ k →
        ∃ d ∈ P.inndiag, ∃ c : C, β = d * fld c) ∧
      (∃ c : C, MulAut.congr e (centerDescend Y ε) = fld c) ∧
      (∀ α : MulAut Y, IsFieldAutThree α → MulAut.congr e (centerDescend Y α) ∈ P.inndiag →
        centerDescend Y α = 1) := by
  rcases hε with hL | hU
  · obtain ⟨F, _, hfin, e, σ, γ, he⟩ := fieldAutPSL3_data hL
    have := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic F
    refine ⟨projectiveSL 3 F, inferInstance, e.trans (γ⁻¹ : MulAut (projectiveSL 3 F)),
      stdPinnedPSL 3 F, goodPinned_psl F, F ≃+* F, inferInstance, this, fieldAut 3 F,
      fun β k hk => ?_, ⟨σ, ?_⟩, fun α hα hin => ?_⟩
    · obtain ⟨A, σ', hA⟩ := mem_semilinearAutGroup_iff.1
        (CFSG.Quasithin.A318P.mem_semilinear_of_orderOf_three_pow hk)
      exact ⟨conjAut 3 F A, by
        rw [stdPinnedPSL_inndiag]; exact conjAut_mem_linearAutGroup A, σ', hA⟩
    · rw [congr_trans', he, congr_self]
      group
    · exact descend_eq_one_of_inndiag_field_model _ _ (goodPinned_psl F) hin hα
  · obtain ⟨p, f, F, _, hF, e, σ, γ, hodd, he⟩ := fieldAutPSU3_data hU
    have hfin := hF.finite
    have hq : 2 < p ^ f := two_lt_pow_of_quasisimple hY hF e
    have := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic F
    refine ⟨unitaryPSU hF 3, inferInstance, e.trans (γ⁻¹ : MulAut (unitaryPSU hF 3)),
      stdPinnedPSU3 hF, goodPinned_psu hF hq, F ≃+* F, inferInstance, this, psuField hF,
      fun β k hk => ?_, ⟨σ, ?_⟩, fun α hα hin => ?_⟩
    · obtain ⟨A, σ', hA⟩ := exists_psuConj_mul_psuField hq β
      exact ⟨psuConj hF A, ⟨A, rfl⟩, σ', hA⟩
    · rw [congr_trans', he, congr_self]
      group
    · exact descend_eq_one_of_inndiag_field_model _ _ (goodPinned_psu hF hq) hin hα

end CFSG.HardMathSupport.Solomon.Coordinator
