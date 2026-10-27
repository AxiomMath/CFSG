module

public import CFSG.CharacterTheory.Semidihedral.ProjectiveSL2Cover
public import CFSG.CharacterTheory.Wreathed.OddFieldFixedTorusDerivedCentralizerSupport

public section

namespace CFSG.Wreathed.NormalComponentLift

open Matrix CFSG.Wreathed.OddFieldTorus

variable {F : Type*} [Field F]

theorem conj_inv_of_anticommute (B X : SpecialLinearGroup (Fin 2) F)
    (hB : B * J₀ F = CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F * J₀ F * B)
    (hX : X ∈ torus F) : B * X * B⁻¹ = X⁻¹ := by
  obtain ⟨v, w, hvw, hXm⟩ := (mem_torus_iff X).mp hX
  have hm := congrArg (fun M : SpecialLinearGroup (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F)) hB
  simp only [SL_coe_mul, J₀_coe, CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity_matrix] at hm
  have h00 := congrFun (congrFun hm 0) 0
  have h01 := congrFun (congrFun hm 0) 1
  have h10 := congrFun (congrFun hm 1) 0
  have h11 := congrFun (congrFun hm 1) 1
  simp only [mul_apply, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one, scalar_apply, diagonal_apply, Fin.isValue] at h00 h01 h10 h11
  norm_num at h00 h01 h10 h11
  suffices hXBX : X * B * X = B by
    have hBX : B * X = X⁻¹ * B := by
      calc B * X = X⁻¹ * (X * B * X) := by group
        _ = X⁻¹ * B := by rw [hXBX]
    rw [hBX, mul_inv_cancel_right]
  apply SL_ext
  rw [SL_coe_mul, SL_coe_mul, hXm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [mul_apply, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero, cons_val_one,
      empty_val', cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue, h11, h10] <;>
    first
      | linear_combination ((B : Matrix (Fin 2) (Fin 2) F) 0 0) * hvw
      | linear_combination ((B : Matrix (Fin 2) (Fin 2) F) 0 1) * hvw
      | linear_combination (-(B : Matrix (Fin 2) (Fin 2) F) 0 0) * hvw

end CFSG.Wreathed.NormalComponentLift
