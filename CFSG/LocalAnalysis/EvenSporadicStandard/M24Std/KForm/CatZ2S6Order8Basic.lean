module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Transport

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm

open Subgroup CFSG.ComponentClassification.CatFC
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def Order8Stmt {S : Type} [Group S] (σ : MulAut S) : Prop :=
  ∀ D : Subgroup ↥(fixedSubgroup σ), A6Hyp σ D → σ ∉ (MulAut.conj : S →* MulAut S).range →
    Nat.card ↥(fixedSubgroup σ) ≤ 720 → ∃ x : ↥(fixedSubgroup σ), orderOf x = 8

@[expose] def HasOrder8 {S : Type} [Group S] (σ : MulAut S) : Prop :=
  ∃ x : ↥(fixedSubgroup σ), orderOf x = 8

theorem HasOrder8.congr {S S' : Type} [Group S] [Group S'] (e : S ≃* S') {σ : MulAut S}
    (h : HasOrder8 σ) : HasOrder8 (MulAut.congr e σ) := by
  obtain ⟨x, hx⟩ := h
  refine ⟨fixedEquiv e σ x, ?_⟩
  rw [← hx]
  exact orderOf_injective (fixedEquiv e σ).toMonoidHom (fixedEquiv e σ).injective x

end CFSG.EvenSporadicStandard.M24Std.KForm
