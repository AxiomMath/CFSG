module

public import Mathlib.LinearAlgebra.Matrix.IsDiag

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Matrix
open scoped Classical

set_option linter.unusedSectionVars false

section Ext

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {R : Type}
  [CommRing R]

abbrev Compl (θ : ι → κ) : Type := {a : κ // a ∉ Set.range θ}

@[expose] noncomputable def sumComplEquiv (θ : ι → κ) (hθ : Function.Injective θ) :
    ι ⊕ Compl θ ≃ κ :=
  Equiv.ofBijective (Sum.elim θ Subtype.val) ⟨by
    rintro (i | x) (j | y) hxy
    · exact congrArg Sum.inl (hθ hxy)
    · exact absurd ⟨i, hxy⟩ y.2
    · exact absurd ⟨j, hxy.symm⟩ x.2
    · exact congrArg Sum.inr (Subtype.ext hxy), fun a => by
    by_cases ha : a ∈ Set.range θ
    · obtain ⟨i, rfl⟩ := ha
      exact ⟨.inl i, rfl⟩
    · exact ⟨.inr ⟨a, ha⟩, rfl⟩⟩

variable (θ : ι → κ) (hθ : Function.Injective θ)

@[simp] theorem sumComplEquiv_inl (i : ι) : sumComplEquiv θ hθ (.inl i) = θ i := rfl

@[simp] theorem sumComplEquiv_inr (x : Compl θ) : sumComplEquiv θ hθ (.inr x) = x.1 := rfl

@[simp] theorem sumComplEquiv_symm_map (i : ι) : (sumComplEquiv θ hθ).symm (θ i) = .inl i := by
  rw [Equiv.symm_apply_eq]
  rfl

theorem sumComplEquiv_symm_of_not {a : κ} (ha : a ∉ Set.range θ) :
    (sumComplEquiv θ hθ).symm a = .inr ⟨a, ha⟩ := by
  rw [Equiv.symm_apply_eq]
  rfl

@[expose] noncomputable def extId (M : Matrix ι ι R) : Matrix κ κ R :=
  (fromBlocks M 0 0 (1 : Matrix (Compl θ) (Compl θ) R)).submatrix (sumComplEquiv θ hθ).symm
    (sumComplEquiv θ hθ).symm

variable (M N : Matrix ι ι R)

theorem extId_mul : extId θ hθ (M * N) = extId θ hθ M * extId θ hθ N := by
  simp only [extId]
  rw [submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem extId_one : extId θ hθ (1 : Matrix ι ι R) = 1 := by
  simp [extId, fromBlocks_one]

theorem det_extId : (extId θ hθ M).det = M.det := by
  simp [extId]

theorem extId_apply_map (i j : ι) : extId θ hθ M (θ i) (θ j) = M i j := by
  simp [extId]

theorem extId_apply_of_not_left {a : κ} (ha : a ∉ Set.range θ) (b : κ) :
    extId θ hθ M a b = (1 : Matrix κ κ R) a b := by
  simp only [extId, submatrix_apply, sumComplEquiv_symm_of_not θ hθ ha]
  by_cases hb : b ∈ Set.range θ
  · obtain ⟨j, rfl⟩ := hb
    have : a ≠ θ j := fun h => ha ⟨j, h.symm⟩
    simp [one_apply, this]
  · rw [sumComplEquiv_symm_of_not θ hθ hb]
    simp [one_apply, Subtype.ext_iff]

theorem extId_apply_of_not_right (a : κ) {b : κ} (hb : b ∉ Set.range θ) :
    extId θ hθ M a b = (1 : Matrix κ κ R) a b := by
  simp only [extId, submatrix_apply, sumComplEquiv_symm_of_not θ hθ hb]
  by_cases ha : a ∈ Set.range θ
  · obtain ⟨i, rfl⟩ := ha
    have : θ i ≠ b := fun h => hb ⟨i, h⟩
    simp [one_apply, this]
  · rw [sumComplEquiv_symm_of_not θ hθ ha]
    simp [one_apply, Subtype.ext_iff]

theorem extId_apply_eq_zero_of_ne {a b : κ} (hab : a ≠ b)
    (h : a ∉ Set.range θ ∨ b ∉ Set.range θ) : extId θ hθ M a b = 0 := by
  rcases h with h | h
  · rw [extId_apply_of_not_left θ hθ M h, one_apply_ne hab]
  · rw [extId_apply_of_not_right θ hθ M _ h, one_apply_ne hab]

theorem extId_isometry (σ : R →+* R) (J : Matrix κ κ R) (J' : Matrix ι ι R)
    (h₁ : ∀ i j, J (θ i) (θ j) = J' i j) (h₂ : ∀ i y, y ∉ Set.range θ → J (θ i) y = 0)
    (h₃ : ∀ i y, y ∉ Set.range θ → J y (θ i) = 0) (hM : (M.map σ)ᵀ * J' * M = J') :
    ((extId θ hθ M).map σ)ᵀ * J * extId θ hθ M = J := by
  have hJ : J = (fromBlocks J' 0 0 (J.submatrix Subtype.val Subtype.val :
      Matrix (Compl θ) (Compl θ) R)).submatrix (sumComplEquiv θ hθ).symm
        (sumComplEquiv θ hθ).symm := by
    ext a b
    obtain ⟨s, rfl⟩ := (sumComplEquiv θ hθ).surjective a
    obtain ⟨t, rfl⟩ := (sumComplEquiv θ hθ).surjective b
    simp only [submatrix_apply, Equiv.symm_apply_apply]
    rcases s with i | x <;> rcases t with j | y
    · simp [h₁]
    · simpa using h₂ i y.1 y.2
    · simpa using h₃ j x.1 x.2
    · simp
  conv_lhs => enter [1, 2]; rw [hJ]
  have h0 : (0 : Matrix ι (Compl θ) R).map σ = 0 := Matrix.map_zero _ (map_zero σ)
  have h0' : (0 : Matrix (Compl θ) ι R).map σ = 0 := Matrix.map_zero _ (map_zero σ)
  have h1 : (1 : Matrix (Compl θ) (Compl θ) R).map σ = 1 := Matrix.map_one _ (map_zero σ) (map_one σ)
  simp only [extId, ← submatrix_map, transpose_submatrix, fromBlocks_map, h0, h0', h1,
    fromBlocks_transpose, transpose_zero, transpose_one]
  rw [submatrix_mul_equiv, submatrix_mul_equiv, fromBlocks_multiply, fromBlocks_multiply]
  simp [hM]
  exact hJ.symm

@[expose] noncomputable def extMulHom : Matrix ι ι R →* Matrix κ κ R where
  toFun := extId θ hθ
  map_one' := extId_one θ hθ
  map_mul' := extId_mul θ hθ

@[expose] noncomputable def extGL : (Matrix ι ι R)ˣ →* (Matrix κ κ R)ˣ :=
  Units.map (extMulHom θ hθ)

theorem coe_extGL (g : (Matrix ι ι R)ˣ) :
    ((extGL θ hθ g : (Matrix κ κ R)ˣ) : Matrix κ κ R) = extId θ hθ (g : Matrix ι ι R) :=
  rfl

theorem extId_cut (pos : κ → ℕ) {i : ℕ}
    (hM : ∀ a b, i ≤ pos (θ a) → pos (θ b) < i → M a b = 0) (a b : κ) (ha : i ≤ pos a)
    (hb : pos b < i) : extId θ hθ M a b = 0 := by
  have hab : a ≠ b := fun e => by subst e; omega
  by_cases ha' : a ∈ Set.range θ
  · by_cases hb' : b ∈ Set.range θ
    · obtain ⟨x, rfl⟩ := ha'
      obtain ⟨y, rfl⟩ := hb'
      rw [extId_apply_map]
      exact hM x y ha hb
    · exact extId_apply_eq_zero_of_ne θ hθ M hab (Or.inr hb')
  · exact extId_apply_eq_zero_of_ne θ hθ M hab (Or.inl ha')

theorem extId_isDiag (hM : M.IsDiag) : (extId θ hθ M).IsDiag := by
  intro a b hab
  by_cases ha : a ∈ Set.range θ
  · by_cases hb : b ∈ Set.range θ
    · obtain ⟨x, rfl⟩ := ha
      obtain ⟨y, rfl⟩ := hb
      rw [extId_apply_map]
      exact hM fun e => hab (by rw [e])
    · exact extId_apply_eq_zero_of_ne θ hθ M hab (Or.inr hb)
  · exact extId_apply_eq_zero_of_ne θ hθ M hab (Or.inl ha)

end Ext

theorem commute_of_isDiag {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
    {A B : Matrix ι ι R} (hA : Matrix.IsDiag A) (hB : Matrix.IsDiag B) : Commute A B := by
  have h1 := hA.diagonal_diag
  have h2 := hB.diagonal_diag
  show A * B = B * A
  rw [← h1, ← h2, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext x
  exact mul_comm _ _

theorem mul_apply_self_of_isDiag {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
    {A B : Matrix ι ι R} (hA : Matrix.IsDiag A) (hB : Matrix.IsDiag B) (x : ι) :
    (A * B) x x = A x x * B x x := by
  have h1 := hA.diagonal_diag
  have h2 := hB.diagonal_diag
  rw [← h1, ← h2, diagonal_mul_diagonal]
  simp

end CFSG.HardMathSupport.Curtis.UnitaryLevi
