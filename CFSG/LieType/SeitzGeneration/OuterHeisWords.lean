module

public import CFSG.LieType.SeitzGeneration.OutdiagHeis

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix

variable {F : Type*} [Field F]

@[expose] def outerY (γ s : F) : Matrix (Fin 3) (Fin 3) F :=
  !![1 - s, -s - γ, -s - γ; -s, 1 - s, -s - γ; -s, -s, 1 - s]

theorem det_outerY {γ : F} (hγ : γ ^ 2 + 3 * γ + 3 = 0) (s : F) : (outerY γ s).det = 1 := by
  rw [Matrix.det_fin_three]
  simp only [outerY, of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val',
    cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.tail_cons]
  linear_combination (-s) * hγ

@[expose] def outerYSL {γ : F} (hγ : γ ^ 2 + 3 * γ + 3 = 0) (s : F) :
    SpecialLinearGroup (Fin 3) F :=
  ⟨outerY γ s, det_outerY hγ s⟩

theorem outerY_comm {γ s β : F} (h : (β - 1) * s = γ) :
    outerY γ s * heisC β = heisC β * outerY γ s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [outerY, heisC, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | ring1 | linear_combination h | linear_combination (-1) * h

@[expose] def outerPsi (γ : F) : Fin 3 → F := ![γ, -2 * γ - 3, γ + 3]

@[expose] def outerTau (γ c : F) : Matrix (Fin 3) (Fin 3) F :=
  1 - c • vecMulVec ![1, 1, 1] (outerPsi γ)

theorem det_outerTau (γ c : F) : (outerTau γ c).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [outerTau, outerPsi]
  ring

@[expose] def outerTauSL (γ c : F) : SpecialLinearGroup (Fin 3) F :=
  ⟨outerTau γ c, det_outerTau γ c⟩

theorem outerY_eq_tau {γ : F} (hγ : γ ^ 2 + 3 * γ + 3 = 0) (s' c : F) :
    outerY γ (s' + c * γ) = outerTau γ c * outerY γ s' := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [outerY, outerTau, outerPsi, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.one_apply] <;>
    first | ring1 | linear_combination (-c) * hγ | linear_combination c * hγ

theorem outerTau_mul {γ₁ γ₂ : F} (h : γ₁ + γ₂ = -3) (c : F) :
    outerTau γ₁ c * outerTau γ₂ c = 1 + vecMulVec ![1, 1, 1] ![3 * c, 0, -(3 * c)] := by
  have h2 : γ₂ = -3 - γ₁ := by linear_combination h
  subst h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [outerTau, outerPsi, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;> ring

theorem conjUnit_toGL {n : ℕ} (g h : SpecialLinearGroup (Fin n) F) :
    conjUnit (SpecialLinearGroup.toGL g) h = g * h * g⁻¹ := by
  apply Subtype.ext
  rw [conjUnit_coe, ← map_inv]
  rfl

theorem outerYSL_mem_of_conj {K : Subgroup (SpecialLinearGroup (Fin 3) F)} {α b γ s' : F}
    (hb : b ≠ 0) (hγ : γ ^ 2 + 3 * γ + 3 = 0) (hK : FixSL (heisC α) ⊆ K)
    (hdiag : ∀ (a b d : F) (h : a * b * d = 1), diagSL a b d h ∈ K)
    (h : (α * b ^ 3 - 1) * s' = γ) : outerYSL hγ s' ∈ K := by
  have hbb : b⁻¹ * 1 * b = 1 := by field_simp
  have hMN : heisC α *
      ((SpecialLinearGroup.toGL (diagSL b⁻¹ 1 b hbb) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((SpecialLinearGroup.toGL (diagSL b⁻¹ 1 b hbb) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        (b⁻¹ • heisC (α * b ^ 3)) := by
    rw [SpecialLinearGroup.coe_GL_coe_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [heisC, diagSL, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp
  have hY : outerYSL hγ s' ∈ FixSL (b⁻¹ • heisC (α * b ^ 3)) :=
    (mem_FixSL_smul (inv_ne_zero hb)).2 (mem_FixSL_of_mul_comm (outerY_comm h).symm)
  have hk := mem_FixSL_conj (P := SpecialLinearGroup.toGL (diagSL b⁻¹ 1 b hbb))
    (M := heisC α) (N := b⁻¹ • heisC (α * b ^ 3)) hMN hY
  rw [conjUnit_toGL] at hk
  have hkK := hK hk
  have e : outerYSL hγ s' = (diagSL b⁻¹ 1 b hbb)⁻¹ * ((diagSL b⁻¹ 1 b hbb) * outerYSL hγ s' *
      (diagSL b⁻¹ 1 b hbb)⁻¹) * (diagSL b⁻¹ 1 b hbb) := by group
  rw [e]
  exact K.mul_mem (K.mul_mem (K.inv_mem (hdiag _ _ _ hbb)) hkK) (hdiag _ _ _ hbb)

end CFSG.LieType.SeitzGeneration
