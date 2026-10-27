module

public import CFSG.GH74.GLS.LU.Local.SL2Aut2
public import CFSG.GH74.GLS.Stage4.T2SL2C
public import CFSG.GH74.GLS.Stage4.T2CentSL

public section

open CFSG.GH74.GLS.IVK.Lifted CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.Stage4.Rest
  CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.Stage4.Hex
open CFSG.Semidihedral.MatrixCoverData (slConjugation)

namespace CFSG.GH74.GLS.Stage4.Rest.Rem

private theorem pow_four_eq_mul_mul {G : Type*} [Monoid G] (y : G) : y ^ 4 = (y * y) * (y * y) := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]

section Weyl

variable {F : Type} [Field F]

private theorem sl2W_pow_four : (sl2W F) ^ 4 = 1 := by
  rw [pow_four_eq_mul_mul, sl2W_sq, negOne_mul_self]

private theorem slFieldAut_sl2W [Finite F] (σ : F ≃+* F) : slFieldAut σ (sl2W F) = sl2W F := by
  rw [slFieldAut_apply]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end Weyl

theorem exists_outer_diag_of_involution {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h3 : 3 < Nat.card F) (α : MulAut (Matrix.SpecialLinearGroup (Fin 2) F)) (hα : α * α = 1)
    (hfix : ∀ x : Matrix.SpecialLinearGroup (Fin 2) F, α x = x → x ^ 4 = 1 → x * x = 1) :
    ∃ g : GL (Fin 2) F, ¬ IsSquare ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) ∧
      ∀ x : Matrix.SpecialLinearGroup (Fin 2) F,
        ((α x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
          (g : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) *
            ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hσ : (gammaOf hodd h3 α).right = 1 := by
    by_contra hσ
    obtain ⟨β, hβ⟩ := exists_conj_slFieldAut hodd h3 α hα hσ
    have h : α * β = β * slFieldAut (gammaOf hodd h3 α).right := by
      rw [← hβ]
      group
    have hy : α (β (sl2W F)) = β (sl2W F) := by
      have := congrArg (fun γ : MulAut (SL2 F) => γ (sl2W F)) h
      simp only [MulAut.mul_apply] at this
      rw [this, slFieldAut_sl2W]
    have hy4 : (β (sl2W F)) ^ 4 = 1 := by
      rw [← map_pow, sl2W_pow_four, map_one]
    have hyy : β (sl2W F) * β (sl2W F) ≠ 1 := by
      intro hyy
      rw [← map_mul, sl2W_sq] at hyy
      exact negOne_ne_one h2 (β.injective (hyy.trans (map_one β).symm))
    exact hyy (hfix _ hy hy4)
  obtain ⟨G, hG⟩ := eq_slConjugation_of_right_eq_one hodd h3 α hσ
  refine ⟨G, ?_, ?_⟩
  · intro hsq
    rw [Matrix.GeneralLinearGroup.val_det_apply] at hsq
    obtain ⟨y, hy⟩ := exists_conj_eq_slConjugation_of_isSquare_det G hsq
    have hαy : α = MulAut.conj y := hG.trans hy
    have hyfix : α y = y := by
      rw [hαy, MulAut.conj_apply, mul_inv_cancel_right]
    have key : ∀ z : SL2 F, y * (y * z * y⁻¹) * y⁻¹ = z := by
      intro z
      have := congrArg (fun γ : MulAut (SL2 F) => γ z) hα
      simpa [hαy, MulAut.mul_apply, MulAut.conj_apply] using this
    have hyy_center : y * y ∈ Subgroup.center (SL2 F) := by
      rw [Subgroup.mem_center_iff]
      intro z
      calc z * (y * y) = (y * (y * z * y⁻¹) * y⁻¹) * (y * y) := by rw [key z]
        _ = (y * y) * z := by group
    have hy4 : y ^ 4 = 1 := by
      rw [pow_four_eq_mul_mul]
      rcases (t2C_center_sl2 _).1 hyy_center with h | h
      · rw [h, mul_one]
      · rw [h, negOne_mul_self]
    have hyy : y * y = 1 := hfix y hyfix hy4
    have hycenter : y ∈ Subgroup.center (SL2 F) := by
      by_cases h1 : y = 1
      · rw [h1]
        exact Subgroup.one_mem _
      · rw [eq_negOne_of_involution h2 hyy h1]
        exact (t2C_center_sl2 _).2 (Or.inr rfl)
    have hαid : ∀ z : SL2 F, α z = z := by
      intro z
      rw [hαy, MulAut.conj_apply, ← Subgroup.mem_center_iff.1 hycenter z, mul_inv_cancel_right]
    have hW := hfix (sl2W F) (hαid _) sl2W_pow_four
    rw [sl2W_sq] at hW
    exact negOne_ne_one h2 hW
  · intro x
    rw [hG]
    exact slConjugation_coe G x

end CFSG.GH74.GLS.Stage4.Rest.Rem
