module

public import CFSG.LieType.Chevalley.GraphFixedRankOneImage
public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.LocalAnalysis.ComponentInitial

variable {k : Type} [Field k]

theorem WSL_eq_uSL_mul_vSL_mul_uSL : (WSL : SL2 k) = uSL 1 * vSL (-1) * uSL 1 := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL, coe_WSL]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem WSL_mul_WSL : (WSL : SL2 k) * WSL = -1 := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_WSL, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem SL2_opposite_root_scalar_compatibility (hk : ringChar k ≠ 2) (σ : k ≃+* k) (a b : kˣ)
    (T : SL2 k →* SL2 k) (hu : ∀ c, T (uSL c) = uSL ((a : k) * σ c))
    (hl : ∀ c, T (vSL c) = vSL ((b : k) * σ c)) (hneg : T (-1) = -1) :
    a * b = 1 ∧ (a = 1 → ∀ A, T A = Matrix.SpecialLinearGroup.map (σ : k →+* k) A) := by
  have hab : a * b = 1 := by
    have hTN : T WSL = uSL (a : k) * vSL (-(b : k)) * uSL (a : k) := by
      rw [WSL_eq_uSL_mul_vSL_mul_uSL, map_mul, map_mul, hu, hl]
      simp only [map_neg, map_one, mul_one, mul_neg]
    have hsq : T WSL * T WSL = -1 := by
      rw [← map_mul, WSL_mul_WSL, hneg]
    rw [hTN] at hsq
    have h10 := congrArg (fun M : SL2 k => (M : Matrix (Fin 2) (Fin 2) k) 1 0) hsq
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL,
      Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one] at h10
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h10
    have h2 : (2 : k) * ((b : k) * (1 - a * b)) = 0 := by
      linear_combination -h10
    have h1 : (1 : k) - a * b = 0 :=
      (mul_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left (Ring.two_ne_zero hk))).resolve_left
        b.ne_zero
    exact Units.ext (by rw [Units.val_mul, Units.val_one]; linear_combination -h1)
  refine ⟨hab, fun ha A => ?_⟩
  have hb : b = 1 := by
    rw [ha, one_mul] at hab
    exact hab
  have hT : T = Matrix.SpecialLinearGroup.map (σ : k →+* k) :=
    MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower fun g hg => by
      rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · change T (uSL c) = Matrix.SpecialLinearGroup.map (σ : k →+* k) (uSL c)
        rw [hu, ha, Units.val_one, one_mul, map_uSL]
        rfl
      · change T (vSL c) = Matrix.SpecialLinearGroup.map (σ : k →+* k) (vSL c)
        rw [hl, hb, Units.val_one, one_mul, map_vSL]
        rfl
  rw [hT]

end CFSG.LieType.Chevalley
