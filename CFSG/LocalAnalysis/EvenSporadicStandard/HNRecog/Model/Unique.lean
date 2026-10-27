module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Model.Hmod
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HNFactsProof
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Model

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.EvenSporadicStandard.TwoHS CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section Facts

theorem isF5Centralizer_nonempty_mulEquiv_of_facts (hHN : HNCentralizerFacts)
    (H H' : Type) [Group H] [Group H'] (E : Subgroup H) (E' : Subgroup H')
    (h : IsF5Centralizer H E) (h' : IsF5Centralizer H' E') : Nonempty (H ≃* H') := by
  obtain ⟨v, hv, hv2⟩ := h.exists_outer_involution
  obtain ⟨v', hv', hv'2⟩ := h'.exists_outer_involution
  obtain ⟨Ψ, -⟩ := exists_mulEquiv_of_isHSCover hHN h.toIsHSCover h'.toIsHSCover h.index_eq_two
    h'.index_eq_two hv hv2 hv' hv'2
  exact ⟨Ψ⟩

theorem hsCtx_of_isHSCover {H : Type} [Group H] {E : Subgroup H} (h : IsHSCover H E) : HSCtx := by
  haveI := h.finite
  exact HSCtx.of_doubleCover h.perfect h.card_center h.quotient

end Facts

section OfFacts

theorem exists_mulEquiv_hmod_of_isF5Centralizer_of_facts (hHN : HNCentralizerFacts)
    (hΛ : HSCtx) {H : Type} [Group H] {E : Subgroup H} (h : IsF5Centralizer H E) :
    ∃ Ψ : H ≃* hΛ.Hmod, ∀ x : H, x ∈ E ↔ Ψ x ∈ hΛ.Emod := by
  obtain ⟨v, hv, hv2⟩ := h.exists_outer_involution
  obtain ⟨Ψ, hΨ⟩ := exists_mulEquiv_of_isHSCover hHN h.toIsHSCover hΛ.isHSCover h.index_eq_two
    hΛ.Emod_index hv hv2 hΛ.yMod_not_mem (by rw [sq]; exact hΛ.yMod_mul_self)
  exact ⟨Ψ, hΨ⟩

theorem exists_mulEquiv_p1408_of_isF5Centralizer_of_facts (hHN : HNCentralizerFacts)
    {H : Type} [Group H] {E : Subgroup H} (h : IsF5Centralizer H E) :
    ∃ Ψ : H ≃* P1408,
      ∀ x : H, x ∈ E ↔ ((Ψ x : P1408) : Equiv.Perm (Fin 1408)) ∈ blocks1408 := by
  let hΛ : HSCtx := hsCtx_of_isHSCover h.toIsHSCover
  obtain ⟨Ψ, hΨ⟩ := exists_mulEquiv_hmod_of_isF5Centralizer_of_facts hHN hΛ h
  refine ⟨Ψ.trans (hmod1408Equiv hΛ), fun x => ?_⟩
  rw [MulEquiv.trans_apply, hΨ x, hmod1408Equiv_mem_Emod_iff]

end OfFacts

section Unique

theorem isF5Centralizer_nonempty_mulEquiv
    (H H' : Type) [Group H] [Group H'] (E : Subgroup H) (E' : Subgroup H')
    (h : IsF5Centralizer H E) (h' : IsF5Centralizer H' E') : Nonempty (H ≃* H') := by
  exact isF5Centralizer_nonempty_mulEquiv_of_facts hnCentralizerFacts H H' E E' h h'

end Unique

section Model

theorem exists_mulEquiv_p1408_of_isF5Centralizer {H : Type} [Group H] {E : Subgroup H}
    (h : IsF5Centralizer H E) :
    ∃ Ψ : H ≃* P1408,
      ∀ x : H, x ∈ E ↔ ((Ψ x : P1408) : Equiv.Perm (Fin 1408)) ∈ blocks1408 := by
  exact exists_mulEquiv_p1408_of_isF5Centralizer_of_facts hnCentralizerFacts h

end Model

end CFSG.EvenSporadicStandard.HNRecog
