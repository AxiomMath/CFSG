module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

namespace CFSG.SeitzReduction

namespace ClassicalLagrangian

open Matrix

section Module

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem apply_eq_smul_of_mem {A N : Module.End R V} {W : Submodule R V} {c : R}
    (hWN : W ≤ LinearMap.range N) (hNW : W ≤ LinearMap.ker N) (hAN : A * N = N * A)
    (hA : ∀ v, A v - c • v ∈ W) {w : V} (hw : w ∈ W) : A w = c • w := by
  obtain ⟨v, rfl⟩ := hWN hw
  have h1 : A (N v) = N (A v) := LinearMap.congr_fun hAN v
  have h2 : N (A v - c • v) = 0 := hNW (hA v)
  rw [map_sub, map_smul, sub_eq_zero] at h2
  rw [h1, h2]

theorem sub_smul_mul_self_eq_zero {A N : Module.End R V} {W : Submodule R V} {c : R}
    (hWN : W ≤ LinearMap.range N) (hNW : W ≤ LinearMap.ker N) (hAN : A * N = N * A)
    (hA : ∀ v, A v - c • v ∈ W) : (A - c • 1) * (A - c • 1) = 0 := by
  ext v
  have h := apply_eq_smul_of_mem hWN hNW hAN hA (hA v)
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    LinearMap.zero_apply]
  rw [h, sub_self]

theorem mul_self_eq_smul_one [CharP R 2] {A N : Module.End R V} {W : Submodule R V} {c : R}
    (hWN : W ≤ LinearMap.range N) (hNW : W ≤ LinearMap.ker N) (hAN : A * N = N * A)
    (hA : ∀ v, A v - c • v ∈ W) : A * A = (c * c) • 1 := by
  have h := sub_smul_mul_self_eq_zero hWN hNW hAN hA
  have h2 : ∀ x : V, x + x = 0 := fun x => by
    rw [← two_smul R x, CharTwo.two_eq_zero, zero_smul]
  ext v
  have hv := LinearMap.congr_fun h v
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    LinearMap.zero_apply] at hv
  simp only [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply]
  rw [← sub_eq_zero]
  have e : A (A v) - (c * c) • v = (A (A v - c • v) - c • (A v - c • v)) + (c • A v + c • A v) -
      ((c * c) • v + (c * c) • v) := by
    rw [map_sub, map_smul, smul_sub, smul_smul]
    abel
  rw [e, hv, h2 (c • A v), h2 ((c * c) • v), add_zero, sub_zero]

end Module

section Matrix

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_sub_smul_mul_self_eq_zero {A s : Matrix ι ι R} {c : R} (hAs : A * s = s * A)
    (hs : (s - 1) * (s - 1) = 0) (hA : ∀ v, ∃ w, A *ᵥ v - c • v = (s - 1) *ᵥ w) :
    (A - c • 1) * (A - c • 1) = 0 := by
  have hcomm : (A - c • 1) * (s - 1) = (s - 1) * (A - c • 1) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, hAs, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, smul_sub]
    abel
  have hA' : ∀ v, ∃ w, (A - c • 1) *ᵥ v = (s - 1) *ᵥ w := fun v => by
    obtain ⟨w, hw⟩ := hA v
    exact ⟨w, by rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hw]⟩
  rw [Matrix.ext_iff_mulVec]
  intro v
  obtain ⟨w, hw⟩ := hA' v
  obtain ⟨w', hw'⟩ := hA' w
  rw [← Matrix.mulVec_mulVec, hw, Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hw',
    Matrix.mulVec_mulVec, hs, Matrix.zero_mulVec, Matrix.zero_mulVec]

theorem mul_self_eq_smul_one_of_sub_smul [CharP R 2] {X : Matrix ι ι R} {c : R}
    (h : (X - c • 1) * (X - c • 1) = 0) : X * X = (c * c) • 1 := by
  have h2 : ∀ Y : Matrix ι ι R, Y + Y = 0 := fun Y => by
    rw [← two_smul R Y, CharTwo.two_eq_zero, zero_smul]
  have h3 : (X - c • 1) * (X - c • 1) = X * X - (c • X + c • X) + (c * c) • 1 := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, smul_sub, smul_smul]
    abel
  rw [h3, h2, sub_zero] at h
  rw [← sub_eq_zero, sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq]
  exact h

theorem matrix_mul_self_eq_smul_one [CharP R 2] {A s : Matrix ι ι R} {c : R} (hAs : A * s = s * A)
    (hs : (s - 1) * (s - 1) = 0) (hA : ∀ v, ∃ w, A *ᵥ v - c • v = (s - 1) *ᵥ w) :
    A * A = (c * c) • 1 :=
  mul_self_eq_smul_one_of_sub_smul (matrix_sub_smul_mul_self_eq_zero hAs hs hA)

end Matrix

section Blocks

variable {R : Type*} [CommRing R] {m : Type*} [Fintype m] [DecidableEq m]

theorem eq_zero_of_isUnit_mul {S X : Matrix m m R} (hS : IsUnit S) (h : S * X = 0) : X = 0 := by
  obtain ⟨u, rfl⟩ := hS
  calc X = (u⁻¹ : (Matrix m m R)ˣ) * (u * X) := by
        rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    _ = 0 := by rw [h, Matrix.mul_zero]

theorem eq_zero_of_mul_isUnit {S X : Matrix m m R} (hS : IsUnit S) (h : X * S = 0) : X = 0 := by
  obtain ⟨u, rfl⟩ := hS
  calc X = (X * u) * (u⁻¹ : (Matrix m m R)ˣ) := by
        rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    _ = 0 := by rw [h, Matrix.zero_mul]

theorem commute_fromBlocks_one_iff {S : Matrix m m R} (hS : IsUnit S) (a b d a' : Matrix m m R) :
    fromBlocks a b d a' * fromBlocks 1 S 0 1 = fromBlocks 1 S 0 1 * fromBlocks a b d a' ↔
      d = 0 ∧ a * S = S * a' := by
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.one_mul, Matrix.zero_mul, zero_add]
  constructor
  · rintro ⟨h1, h2, -, -⟩
    have hd : d = 0 := eq_zero_of_isUnit_mul hS (by
      have := congrArg (· - a) h1
      simpa using this.symm)
    subst hd
    refine ⟨rfl, ?_⟩
    simpa [add_comm] using h2
  · rintro ⟨rfl, h⟩
    exact ⟨by simp, by rw [h, add_comm], by simp, by simp⟩

theorem commute_fromBlocks_radical_iff (a b a' T : Matrix m m R) :
    fromBlocks a b 0 a' * fromBlocks 1 T 0 1 = fromBlocks 1 T 0 1 * fromBlocks a b 0 a' ↔
      a * T = T * a' := by
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.one_mul, Matrix.zero_mul, zero_add,
    and_true, true_and]
  constructor
  · intro h
    simpa [add_comm] using h
  · intro h
    rw [h, add_comm]

theorem commute_of_commute_fromBlocks_diagonal {a b a' P Q : Matrix m m R}
    (h : fromBlocks a b 0 a' * fromBlocks P 0 0 Q = fromBlocks P 0 0 Q * fromBlocks a b 0 a') :
    a' * Q = Q * a' := by
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h
  simpa using h.2.2.2

theorem commute_inv_mul_iff {S : Matrix m m R} (hS : IsUnit S) {a a' : Matrix m m R}
    (haS : a * S = S * a') (T : Matrix m m R) :
    a * T = T * a' ↔ a' * (S⁻¹ * T) = (S⁻¹ * T) * a' := by
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS
  have h1 : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hdet
  have h2 : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hdet
  have ha : a = S * a' * S⁻¹ := by
    rw [← haS, Matrix.mul_assoc, h1, Matrix.mul_one]
  constructor
  · intro h
    calc a' * (S⁻¹ * T) = S⁻¹ * (S * a' * S⁻¹) * T := by
          simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
      _ = S⁻¹ * T * a' := by rw [← ha, Matrix.mul_assoc, h, ← Matrix.mul_assoc]
  · intro h
    calc a * T = S * (a' * (S⁻¹ * T)) := by rw [ha]; simp only [Matrix.mul_assoc]
      _ = T * a' := by rw [h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem fromBlocks_sub_smul_mul_self_eq_zero {S : Matrix m m R} (hS : IsUnit S)
    {a b a' : Matrix m m R} (haS : a * S = S * a') {c : R} (ha' : a' = c • 1) :
    (fromBlocks a b 0 a' - c • 1) * (fromBlocks a b 0 a' - c • 1) = 0 := by
  have ha : a = c • 1 := by
    have h : (a - c • 1) * S = 0 := by
      rw [Matrix.sub_mul, haS, ha', Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_mul_isUnit hS h)
  have hX : fromBlocks a b 0 a' - c • (1 : Matrix (m ⊕ m) (m ⊕ m) R) = fromBlocks 0 b 0 0 := by
    rw [← fromBlocks_one, fromBlocks_smul, ha, ha', smul_zero]
    ext (i | i) (j | j) <;> simp
  rw [hX, fromBlocks_multiply]
  simp

theorem sub_smul_mul_self_eq_zero_of_commute_fromBlocks {S : Matrix m m R} (hS : IsUnit S)
    {A : Matrix (m ⊕ m) (m ⊕ m) R} (hAs : A * fromBlocks 1 S 0 1 = fromBlocks 1 S 0 1 * A) {c : R}
    (hA : A.toBlocks₂₂ = c • 1) : (A - c • 1) * (A - c • 1) = 0 := by
  rw [← fromBlocks_toBlocks A] at hAs ⊢
  obtain ⟨hd, haS⟩ := (commute_fromBlocks_one_iff hS _ _ _ _).mp hAs
  rw [hd]
  exact fromBlocks_sub_smul_mul_self_eq_zero hS haS hA

theorem mul_self_eq_smul_one_of_commute_fromBlocks [CharP R 2] {S : Matrix m m R} (hS : IsUnit S)
    {A : Matrix (m ⊕ m) (m ⊕ m) R} (hAs : A * fromBlocks 1 S 0 1 = fromBlocks 1 S 0 1 * A) {c : R}
    (hA : A.toBlocks₂₂ = c • 1) : A * A = (c * c) • 1 :=
  mul_self_eq_smul_one_of_sub_smul (sub_smul_mul_self_eq_zero_of_commute_fromBlocks hS hAs hA)

end Blocks

end ClassicalLagrangian

end CFSG.SeitzReduction
