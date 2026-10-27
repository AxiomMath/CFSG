module

public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedInner
public import CFSG.GH74.Generic.S1.FrameDefs

public section

namespace CFSG.GH74.Generic.S1

open Matrix Module CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F]

section Diag

theorem exists_inv_conj_diag (hchar : ringChar F ≠ 2) {B : GL (Fin 4) F} (hB : B * B = 1) :
    ∃ (P : GL (Fin 4) F) (k : ℕ),
      k = finrank F (LinearMap.ker (toLin' (B : Matrix (Fin 4) (Fin 4) F) - 1)) ∧
      ((P⁻¹ * B * P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        Matrix.diagonal (fun i : Fin 4 => if (i : ℕ) < k then (1 : F) else -1) := by
  have hBm : (B : Matrix (Fin 4) (Fin 4) F) * B = 1 := by rw [← Units.val_mul, hB, Units.val_one]
  obtain ⟨b, hb⟩ := exists_eigenbasis hchar hBm
  obtain ⟨P, D, hPD, hD⟩ := exists_gl_inv_mul_mul_eq_toMatrix b B
  set k := finrank F (LinearMap.ker (toLin' (B : Matrix (Fin 4) (Fin 4) F) - 1)) with hk
  set d : Fin 4 → F := fun i => if (i : ℕ) < k then 1 else -1 with hd
  have hDd : (D : Matrix (Fin 4) (Fin 4) F) = diagonal d := by
    rw [hD]
    ext a c
    rw [LinearMap.toMatrix_apply, toLin'_apply, hb c, map_smul, Basis.repr_self,
      Finsupp.smul_apply, Finsupp.single_apply, diagonal_apply]
    by_cases hac : a = c
    · subst hac
      simp [hd]
    · simp [hac, Ne.symm hac]
  exact ⟨P, k, rfl, by rw [hPD]; exact hDd⟩

theorem diag_three_eq_reflDiag :
    (Matrix.diagonal (fun i : Fin 4 => if (i : ℕ) < 3 then (1 : F) else -1) :
      Matrix (Fin 4) (Fin 4) F) = ((reflDiag F 3 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  change _ = reflDiagMat F 3
  unfold reflDiagMat
  congr 1
  funext i
  fin_cases i <;> simp

theorem k_odd_of_det (hchar : ringChar F ≠ 2) {B : GL (Fin 4) F} {k : ℕ} (hk4 : k ≤ 4)
    (hdet : (B : Matrix (Fin 4) (Fin 4) F).det = -1) {P : GL (Fin 4) F}
    (hP : ((P⁻¹ * B * P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        Matrix.diagonal (fun i : Fin 4 => if (i : ℕ) < k then (1 : F) else -1)) :
    k = 1 ∨ k = 3 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
  have hd : ((P⁻¹ * B * P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = -1 := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hdet]
    have h1 : (P⁻¹ : GL (Fin 4) F).val.det * (P : Matrix (Fin 4) (Fin 4) F).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    calc (P⁻¹ : GL (Fin 4) F).val.det * -1 * (P : Matrix (Fin 4) (Fin 4) F).det
        = -((P⁻¹ : GL (Fin 4) F).val.det * (P : Matrix (Fin 4) (Fin 4) F).det) := by ring
      _ = -1 := by rw [h1]
  rw [hP, Matrix.det_diagonal, Fin.prod_univ_four] at hd
  interval_cases k <;> simp at hd ⊢ <;> (apply h2; linear_combination hd)

theorem exists_refl_conj (hchar : ringChar F ≠ 2) {ρ : GL (Fin 4) F} (hρ : ρ * ρ = 1)
    (hdet : (ρ : Matrix (Fin 4) (Fin 4) F).det = -1) :
    ∃ (ρ' P : GL (Fin 4) F), (ρ' = ρ ∨ ρ' = -ρ) ∧ P⁻¹ * ρ' * P = reflDiag F 3 ∧
      finrank F (LinearMap.ker (toLin' (ρ' : Matrix (Fin 4) (Fin 4) F) - 1)) = 3 := by
  obtain ⟨P₀, k, hk, hP₀⟩ := exists_inv_conj_diag hchar hρ
  have hρm : (ρ : Matrix (Fin 4) (Fin 4) F) * ρ = 1 := by rw [← Units.val_mul, hρ, Units.val_one]
  have hk4 : k ≤ 4 := by
    rw [hk]
    calc finrank F (LinearMap.ker (toLin' (ρ : Matrix (Fin 4) (Fin 4) F) - 1))
        ≤ finrank F (Fin 4 → F) := Submodule.finrank_le _
      _ = 4 := by simp
  rcases k_odd_of_det hchar hk4 hdet hP₀ with h1 | h3
  · have hneg : (-ρ) * (-ρ) = 1 := by rw [neg_mul_neg, hρ]
    obtain ⟨P₁, k₁, hk₁, hP₁⟩ := exists_inv_conj_diag hchar hneg
    have hsum := Submodule.finrank_add_eq_of_isCompl (isCompl_eigenspaces hchar hρm)
    rw [finrank_fin_fun] at hsum
    have hker : LinearMap.ker (toLin' ((-ρ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) - 1) =
        LinearMap.ker (toLin' (ρ : Matrix (Fin 4) (Fin 4) F) + 1) := by
      ext v
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.add_apply, toLin'_apply,
        Module.End.one_apply, Units.val_neg, neg_mulVec]
      rw [← neg_add', neg_eq_zero]
    have hk₁3 : k₁ = 3 := by
      rw [hk₁, hker]
      omega
    refine ⟨-ρ, P₁, Or.inr rfl, Units.ext ?_, hk₁ ▸ hk₁3⟩
    rw [hP₁, hk₁3, diag_three_eq_reflDiag]
  · refine ⟨ρ, P₀, Or.inl rfl, Units.ext ?_, hk ▸ h3⟩
    rw [hP₀, h3, diag_three_eq_reflDiag]

end Diag

section Conj

@[expose] def conjEquiv (S : Subgroup (GL (Fin 4) F)) (P : GL (Fin 4) F)
    (h1 : ∀ k ∈ S, P⁻¹ * k * P ∈ S) (h2 : ∀ k ∈ S, P * k * P⁻¹ ∈ S) : ↥S ≃* ↥S where
  toFun k := ⟨P⁻¹ * (k : GL (Fin 4) F) * P, h1 k k.2⟩
  invFun k := ⟨P * (k : GL (Fin 4) F) * P⁻¹, h2 k k.2⟩
  left_inv k := Subtype.ext (by simp [mul_assoc])
  right_inv k := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by
    change P⁻¹ * ((a : GL (Fin 4) F) * (b : GL (Fin 4) F)) * P = _
    simp [mul_assoc])

theorem conjEquiv_apply (S : Subgroup (GL (Fin 4) F)) (P : GL (Fin 4) F)
    (h1 : ∀ k ∈ S, P⁻¹ * k * P ∈ S) (h2 : ∀ k ∈ S, P * k * P⁻¹ ∈ S) (k : ↥S) :
    ((conjEquiv S P h1 h2 k : ↥S) : GL (Fin 4) F) = P⁻¹ * (k : GL (Fin 4) F) * P := rfl

theorem conj_mem_statedSL (P : GL (Fin 4) F) {k : GL (Fin 4) F} (hk : k ∈ StatedSL 4 F) :
    P⁻¹ * k * P ∈ StatedSL 4 F := by
  rw [statedSL_eq_detOne, mem_detOne] at hk ⊢
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hk, mul_one]
  rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]

theorem neg_conj_eq (u X : GL (Fin 4) F) : (-u) * X * (-u)⁻¹ = u * X * u⁻¹ := by
  have h : (-u)⁻¹ = -u⁻¹ := by
    apply inv_eq_of_mul_eq_one_right
    rw [neg_mul_neg, mul_inv_cancel]
  rw [h, neg_mul, mul_neg, neg_mul, neg_neg]

theorem exists_normalized_iso {K : Type*} [Group K] {S : Subgroup (GL (Fin 4) F)} (e₀ : K ≃* ↥S)
    (α : MulAut K) {ρ ρ' P : GL (Fin 4) F} (hρ' : ρ' = ρ ∨ ρ' = -ρ)
    (hact : ∀ n : K, ((e₀ (α n) : ↥S) : GL (Fin 4) F) = ρ * ((e₀ n : ↥S) : GL (Fin 4) F) * ρ⁻¹)
    (hP : P⁻¹ * ρ' * P = reflDiag F 3) (h1 : ∀ k ∈ S, P⁻¹ * k * P ∈ S)
    (h2 : ∀ k ∈ S, P * k * P⁻¹ ∈ S) :
    ∃ e₁ : K ≃* ↥S,
      (∀ n : K, ((e₁ (α n) : ↥S) : GL (Fin 4) F) =
        reflDiag F 3 * ((e₁ n : ↥S) : GL (Fin 4) F) * (reflDiag F 3)⁻¹) ∧
      ∀ n : K, ((e₁ n : ↥S) : GL (Fin 4) F) = P⁻¹ * ((e₀ n : ↥S) : GL (Fin 4) F) * P := by
  refine ⟨e₀.trans (conjEquiv S P h1 h2), fun n => ?_, fun n => rfl⟩
  have hconj : ∀ X : GL (Fin 4) F, ρ * X * ρ⁻¹ = ρ' * X * ρ'⁻¹ := by
    intro X
    rcases hρ' with h | h
    · rw [h]
    · rw [h, neg_conj_eq]
  change P⁻¹ * ((e₀ (α n) : ↥S) : GL (Fin 4) F) * P = _ * (P⁻¹ * ((e₀ n : ↥S) : GL (Fin 4) F) * P) *
    _
  rw [hact n, hconj, ← hP]
  group

end Conj

end CFSG.GH74.Generic.S1
