module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B514Key

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma514_of (h37 : Asc82Lemma37) (h513 : Asc82Lemma513) : Asc82Lemma514 := by
  intro G _ _ t L S z r B A K₁ K₂ h c
  have hAB : ⁅K₁ ⊔ K₂, CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h⁆ = ⊥ :=
    sec5b_514_key h37 h513 c
  have hcomm23 : ⁅CFSG.conjugate K₁ h, CFSG.conjugate K₂ h⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (c.comm₃₄ a ha b hb).symm
  refine ⟨hAB, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [Kfam5, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three]
    · exact absurd rfl hij
    · exact c.comm
    · exact eq_bot_iff.mpr
        ((Subgroup.commutator_mono le_sup_left le_sup_left).trans (le_of_eq hAB))
    · exact eq_bot_iff.mpr
        ((Subgroup.commutator_mono le_sup_left le_sup_right).trans (le_of_eq hAB))
    · rw [Subgroup.commutator_comm]; exact c.comm
    · exact absurd rfl hij
    · exact eq_bot_iff.mpr
        ((Subgroup.commutator_mono le_sup_right le_sup_left).trans (le_of_eq hAB))
    · exact eq_bot_iff.mpr
        ((Subgroup.commutator_mono le_sup_right le_sup_right).trans (le_of_eq hAB))
    · rw [Subgroup.commutator_comm]
      exact eq_bot_iff.mpr
        ((Subgroup.commutator_mono le_sup_left le_sup_left).trans (le_of_eq hAB))
    · rw [Subgroup.commutator_comm]
      exact eq_bot_iff.mpr
        ((Subgroup.commutator_mono le_sup_right le_sup_left).trans (le_of_eq hAB))
    · exact absurd rfl hij
    · exact hcomm23
    · rw [Subgroup.commutator_comm]
      exact eq_bot_iff.mpr
        ((Subgroup.commutator_mono le_sup_left le_sup_right).trans (le_of_eq hAB))
    · rw [Subgroup.commutator_comm]
      exact eq_bot_iff.mpr
        ((Subgroup.commutator_mono le_sup_right le_sup_right).trans (le_of_eq hAB))
    · rw [Subgroup.commutator_comm]; exact hcomm23
    · exact absurd rfl hij
  · intro i
    fin_cases i <;> simp only [Kfam5, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three]
    · exact c.iso₁
    · exact c.iso₂
    · exact c.iso₃
    · exact c.iso₄

end CFSG.OddStandard.SmallF3.Omega
