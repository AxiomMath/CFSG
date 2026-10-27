module

public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.CGT.PushingUpLit.T2KR.P613

section F4

variable {F : Type} [Field F] [CharP F 2]

theorem two_eq_zero : (2 : F) = 0 := CharP.cast_eq_zero F 2

theorem f4_cases [Fintype F] (hF : Fintype.card F = 4) (a : F) :
    a = 0 ∨ a = 1 ∨ a ^ 2 + a + 1 = 0 := by
  have h4 : a ^ 4 = a := by simpa [hF] using FiniteField.pow_card a
  by_cases ha : a = 0
  · exact Or.inl ha
  by_cases ha1 : a = 1
  · exact Or.inr (Or.inl ha1)
  right; right
  have h3 : a ^ 3 = 1 := by
    have : a * (a ^ 3 - 1) = 0 := by linear_combination h4
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h ha
    · linear_combination h
  have hne : a + 1 ≠ 0 := by
    intro h
    apply ha1
    linear_combination h - (two_eq_zero (F := F))
  have : (a + 1) * (a ^ 2 + a + 1) = (a + 1) * 0 := by
    linear_combination h3 + (a ^ 2 + a + 1) * (two_eq_zero (F := F))
  exact mul_left_cancel₀ hne this

omit [CharP F 2] in
theorem root_cases {ω y : F} (hω : ω ^ 2 + ω + 1 = 0) (hy : y ^ 2 + y + 1 = 0) :
    y = ω ∨ y = ω ^ 2 := by
  have : (y - ω) * (y - ω ^ 2) = 0 := by linear_combination hy + (ω - 1 - y) * hω
  rcases mul_eq_zero.1 this with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr (sub_eq_zero.1 h)

theorem root_sq {ω : F} (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 2 = ω + 1 := by
  linear_combination hω - (ω + 1) * (two_eq_zero (F := F))

omit [CharP F 2] in
theorem root_cube {ω : F} (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 3 = 1 := by
  linear_combination (ω - 1) * hω

omit [CharP F 2] in
theorem root_ne_zero {ω : F} (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 0 := by
  rintro rfl
  simp at hω

theorem frob_eq_sq [Fintype F] (hF : Fintype.card F = 4) (σ : F ≃+* F) (hσ : σ ≠ 1) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) : σ ω = ω ^ 2 := by
  have hσω : (σ ω) ^ 2 + σ ω + 1 = 0 := by
    have := congrArg σ hω
    simpa [map_add, map_pow] using this
  rcases root_cases hω hσω with h | h
  · exfalso
    apply hσ
    refine RingEquiv.ext fun a => ?_
    rcases f4_cases hF a with ha | ha | ha
    · subst ha; simp
    · subst ha; simp
    · rcases root_cases hω ha with h' | h'
      · rw [h']; simpa using h
      · rw [h']; simp [h]
  · exact h

end F4

section Descent

variable {F W : Type} [Field F] [CharP F 2] [AddCommGroup W] [Module F W]

theorem exists_fixed_decomp (σ : F ≃+* F) {ω : F} (hω : ω + σ ω = 1) (β : W →+ W)
    (hβ : ∀ (c : F) (w : W), β (c • w) = σ c • β w) (hββ : ∀ w, β (β w) = w) (w : W) :
    ∃ c c' : W, β c = c ∧ β c' = c' ∧ w = c + ω • c' := by
  have h2 : (2 : F) = 0 := two_eq_zero
  have hσω : σ ω = 1 + ω := by linear_combination hω - ω * h2
  have h3 : ∀ x : W, (2 : F) • x = 0 := fun x => by rw [h2, zero_smul]
  refine ⟨(1 + ω) • w + ω • β w, w + β w, ?_, ?_, ?_⟩
  · rw [map_add, hβ, hβ, hββ, map_add, map_one, hσω]
    linear_combination (norm := module) h3 (β w)
  · rw [map_add, hββ, add_comm]
  · linear_combination (norm := module) (-ω) • h3 w - ω • h3 (β w)

end Descent

section Torus

variable {F : Type} [Field F]

@[expose] def colMat (e₁ e₂ : Fin 2 → F) : Matrix (Fin 2) (Fin 2) F :=
  !![e₁ 0, e₂ 0; e₁ 1, e₂ 1]

theorem det_colMat (e₁ e₂ : Fin 2 → F) :
    (colMat e₁ e₂).det = e₁ 0 * e₂ 1 - e₂ 0 * e₁ 1 := by
  simp [colMat, Matrix.det_fin_two_of]

theorem colMat_mulVec_left (e₁ e₂ : Fin 2 → F) : (colMat e₁ e₂).mulVec ![1, 0] = e₁ := by
  ext i
  fin_cases i <;> simp [colMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem colMat_mulVec_right (e₁ e₂ : Fin 2 → F) : (colMat e₁ e₂).mulVec ![0, 1] = e₂ := by
  ext i
  fin_cases i <;> simp [colMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_torus_matrix (e₁ e₂ : Fin 2 → F) (hdet : e₁ 0 * e₂ 1 - e₂ 0 * e₁ 1 ≠ 0) {l : F}
    (hl : l ≠ 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) F,
      (g : Matrix (Fin 2) (Fin 2) F).mulVec e₁ = l • e₁ ∧
        (g : Matrix (Fin 2) (Fin 2) F).mulVec e₂ = l⁻¹ • e₂ := by
  set P := colMat e₁ e₂ with hP
  have hPu : IsUnit P.det := by
    rw [hP, det_colMat]
    exact isUnit_iff_ne_zero.2 hdet
  set Dm : Matrix (Fin 2) (Fin 2) F := !![l, 0; 0, l⁻¹] with hD
  have hDdet : Dm.det = 1 := by
    simp [hD, Matrix.det_fin_two_of, hl]
  have hdetg : (P * Dm * P⁻¹).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, hDdet]
    obtain ⟨u, hu⟩ := hPu
    rw [← hu]
    simp
  refine ⟨⟨P * Dm * P⁻¹, hdetg⟩, ?_, ?_⟩
  · show (P * Dm * P⁻¹).mulVec e₁ = l • e₁
    rw [← colMat_mulVec_left e₁ e₂, ← hP, Matrix.mulVec_mulVec, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hPu, Matrix.mul_one, ← Matrix.mulVec_mulVec]
    have : Dm.mulVec ![1, 0] = l • ![1, 0] := by
      ext i
      fin_cases i <;> simp [hD, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [this, Matrix.mulVec_smul, hP, colMat_mulVec_left]
  · show (P * Dm * P⁻¹).mulVec e₂ = l⁻¹ • e₂
    rw [← colMat_mulVec_right e₁ e₂, ← hP, Matrix.mulVec_mulVec, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hPu, Matrix.mul_one, ← Matrix.mulVec_mulVec]
    have : Dm.mulVec ![0, 1] = l⁻¹ • ![0, 1] := by
      ext i
      fin_cases i <;> simp [hD, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [this, Matrix.mulVec_smul, hP, colMat_mulVec_right]

end Torus

end CFSG.CGT.PushingUpLit.T2KR.P613
