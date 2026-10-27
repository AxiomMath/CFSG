module

public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardRowCoordinates

public section

open Matrix Subgroup
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

namespace CFSG.ComponentClassification.GS79bSec5

theorem leviOne_mem_normalizer_unipOne
    {F : Type} [Field F]
    (B : Matrix.SpecialLinearGroup (Fin 2) F) :
    CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F B ∈
      Subgroup.normalizer
        (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F :
          Set (Matrix.SpecialLinearGroup (Fin 3) F)) := by
  refine CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.mem_normalizer_of_conj_mem ?_ ?_
  · intro x hx
    rw [← rowSLHom_range F] at hx ⊢
    obtain ⟨v, rfl⟩ := hx
    rw [leviOne_conj_rowSLHom]
    exact ⟨Multiplicative.ofAdd
      ((B : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd v), rfl⟩
  · intro x hx
    rw [← rowSLHom_range F] at hx ⊢
    obtain ⟨v, rfl⟩ := hx
    have h : CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F B⁻¹ *
        rowSLHom F v * (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.leviOne F B⁻¹)⁻¹ ∈
        (rowSLHom F).range := by
      rw [leviOne_conj_rowSLHom]
      exact ⟨Multiplicative.ofAdd
        (((B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ
          Multiplicative.toAdd v), rfl⟩
    simpa [map_inv] using h

end CFSG.ComponentClassification.GS79bSec5
