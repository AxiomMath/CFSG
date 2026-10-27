module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.L3.Conj
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

open Matrix

variable {F : Type} [Field F]

local notation "sc" => Matrix.GeneralLinearGroup.scalar (Fin 3)

private theorem exists_scalar_of_mem_center {g : GL (Fin 3) F}
    (hg : g ∈ Subgroup.center (GL (Fin 3) F)) : ∃ u : Fˣ, g = sc u := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg
  obtain ⟨u, rfl⟩ := hg
  exact ⟨u, rfl⟩

private theorem scalar_mem_center (u : Fˣ) : sc u ∈ Subgroup.center (GL (Fin 3) F) := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨u, rfl⟩

private theorem scalar_injective : Function.Injective (sc : Fˣ → GL (Fin 3) F) := by
  intro u w h
  have := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F) 0 0) h
  exact Units.ext (by simpa [Matrix.GeneralLinearGroup.coe_scalar] using this)

private theorem det_scalar (u : Fˣ) : Matrix.GeneralLinearGroup.det (sc u) = u ^ 3 := by
  ext
  simp [pow_three]

private theorem commutator_scalar {g h : GL (Fin 3) F}
    (hc : g * h * g⁻¹ * h⁻¹ ∈ Subgroup.center (GL (Fin 3) F)) :
    ∃ ω : Fˣ, g * h * g⁻¹ * h⁻¹ = sc ω ∧ ω ^ 3 = 1 := by
  obtain ⟨ω, hω⟩ := exists_scalar_of_mem_center hc
  refine ⟨ω, hω, ?_⟩
  have hdet := congrArg Matrix.GeneralLinearGroup.det hω
  rw [det_scalar, map_mul, map_mul, map_mul, map_inv, map_inv,
    mul_right_comm (Matrix.GeneralLinearGroup.det g)] at hdet
  simpa using hdet.symm

private theorem conj_pow_eq {G : Type*} [Group G] {x y c : G} (hc : c ∈ Subgroup.center G)
    (h : x * y * x⁻¹ = c * y) (k : ℕ) : x ^ k * y * (x ^ k)⁻¹ = c ^ k * y := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hck := Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hc k) x
    calc x ^ (k + 1) * y * (x ^ (k + 1))⁻¹ = x * (x ^ k * y * (x ^ k)⁻¹) * x⁻¹ := by group
      _ = x * c ^ k * y * x⁻¹ := by rw [ih]; group
      _ = c ^ k * (x * y * x⁻¹) := by rw [hck]; group
      _ = c ^ (k + 1) * y := by rw [h, pow_succ]; group

private theorem mul_pow_three_of_comm {G : Type*} [Group G] {x y c : G}
    (hc : c ∈ Subgroup.center G) (h : x * y * x⁻¹ = c * y) (hc3 : c ^ 3 = 1) :
    (x * y) ^ 3 = y ^ 3 * x ^ 3 := by
  have h2 := conj_pow_eq hc h 2
  have h3 := conj_pow_eq hc h 3
  have hcy := Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hc 2) y
  calc (x * y) ^ 3 = (x * y * x⁻¹) * (x ^ 2 * y * (x ^ 2)⁻¹) * (x ^ 3 * y * (x ^ 3)⁻¹) * x ^ 3 := by
        simp only [pow_succ, pow_zero, one_mul]; group
    _ = c * (y * c ^ 2) * y * y * x ^ 3 := by rw [h, h2, h3, hc3]; group
    _ = c ^ 3 * y ^ 3 * x ^ 3 := by
      rw [hcy]; simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = y ^ 3 * x ^ 3 := by rw [hc3, one_mul]

private theorem cube_dichotomy_units [Finite F] {l m : Fˣ} (hl : ¬ ∃ k : Fˣ, k ^ 3 = l)
    (hm : ¬ ∃ k : Fˣ, k ^ 3 = m) : (∃ k : Fˣ, k ^ 3 = l * m) ∨ ∃ k : Fˣ, k ^ 3 = l * m ^ 2 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg l)
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg m)
  have hcube : ∀ n : ℤ, (3 : ℤ) ∣ n → ∃ k : Fˣ, k ^ 3 = g ^ n := by
    rintro n ⟨t, rfl⟩
    exact ⟨g ^ t, by rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm]; rfl⟩
  have hi : ¬ (3 : ℤ) ∣ i := fun h => hl (hcube i h)
  have hj : ¬ (3 : ℤ) ∣ j := fun h => hm (hcube j h)
  have key : (3 : ℤ) ∣ i + j ∨ (3 : ℤ) ∣ i + 2 * j := by
    have h1 : i % 3 = 1 ∨ i % 3 = 2 := by omega
    have h2 : j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> omega
  rcases key with h | h
  · left; rw [← _root_.zpow_add]; exact hcube _ h
  · right
    rw [← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_add]
    exact hcube _ (by simpa [mul_comm] using h)

private theorem omega_sq_add (ζ : Fˣ) (hζ : ζ ≠ 1) (hζ3 : ζ ^ 3 = 1) :
    (ζ : F) ^ 2 + ζ + 1 = 0 := by
  have h3 : (ζ : F) ^ 3 = 1 := by simpa using congrArg Units.val hζ3
  have : ((ζ : F) - 1) * ((ζ : F) ^ 2 + ζ + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (Units.ext (by simpa using sub_eq_zero.mp h)) hζ
  · exact h

private theorem exists_eigen_of_pow_three {x : GL (Fin 3) F} {κ ζ : Fˣ} (hζ : ζ ≠ 1)
    (hζ3 : ζ ^ 3 = 1) (hx : x ^ 3 = sc (κ ^ 3)) :
    ∃ β : Fˣ, ∃ v : Fin 3 → F, v ≠ 0 ∧ (x : Matrix (Fin 3) (Fin 3) F) *ᵥ v = (β : F) • v := by
  set M := (x : Matrix (Fin 3) (Fin 3) F)
  have h1 := omega_sq_add ζ hζ hζ3
  have hM3 : M ^ 3 = algebraMap F _ ((κ : F) ^ 3) := by
    rw [← Units.val_pow_eq_pow_val, hx, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.algebraMap_eq_diagonal]
    congr 1
  have hpoly : (Polynomial.X - Polynomial.C (κ : F)) *
      (Polynomial.X - Polynomial.C ((κ * ζ : Fˣ) : F)) *
      (Polynomial.X - Polynomial.C ((κ * ζ ^ 2 : Fˣ) : F)) =
      Polynomial.X ^ 3 - Polynomial.C ((κ : F) ^ 3) := by
    have h1' := congrArg Polynomial.C h1
    have h3' := congrArg Polynomial.C (show (ζ : F) ^ 3 = 1 by simpa using congrArg Units.val hζ3)
    simp only [map_add, map_pow, map_one, map_zero] at h1' h3'
    push_cast
    simp only [map_mul, map_pow]
    linear_combination (Polynomial.C (κ : F) ^ 2 * Polynomial.C (ζ : F) * Polynomial.X -
      Polynomial.C (κ : F) * Polynomial.X ^ 2) * h1' - Polynomial.C (κ : F) ^ 3 * h3'
  have hfac := congrArg (Polynomial.aeval M) hpoly
  simp only [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, map_pow] at hfac
  rw [← map_pow, ← hM3, sub_self] at hfac
  have hdet := congrArg Matrix.det hfac
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_zero] at hdet
  have key : ∀ r : Fˣ, (M - algebraMap F _ (r : F)).det = 0 →
      ∃ β : Fˣ, ∃ v : Fin 3 → F, v ≠ 0 ∧ M *ᵥ v = (β : F) • v := by
    intro r hr
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hr
    refine ⟨r, v, hv, ?_⟩
    rw [Matrix.sub_mulVec, sub_eq_zero, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
      Matrix.one_mulVec] at hMv
    exact hMv
  rcases mul_eq_zero.mp hdet with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact key κ h
    · exact key _ h
  · exact key _ h

private theorem mul_eq_smul_of_commutator {a b : GL (Fin 3) F} {ω : Fˣ}
    (hab : a * b * a⁻¹ * b⁻¹ = sc ω) :
    (a : Matrix (Fin 3) (Fin 3) F) * b = (ω : F) • ((b : Matrix (Fin 3) (Fin 3) F) * a) := by
  have h : a * b = sc ω * (b * a) := by rw [← hab]; group
  rw [← Units.val_mul, h, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul, Units.val_mul]

private theorem mulVec_pow_eigen {M B : Matrix (Fin 3) (Fin 3) F} {ω : F}
    (hMB : M * B = ω • (B * M)) {v : Fin 3 → F} (hv : M *ᵥ v = v) (j : ℕ) :
    M *ᵥ ((B ^ j) *ᵥ v) = ω ^ j • ((B ^ j) *ᵥ v) := by
  induction j with
  | zero => simpa using hv
  | succ j ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hMB, Matrix.smul_mulVec,
      ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, smul_smul, pow_succ, mul_comm]

private def colMat (B : Matrix (Fin 3) (Fin 3) F) (v : Fin 3 → F) : Matrix (Fin 3) (Fin 3) F :=
  (Matrix.of fun j : Fin 3 => (B ^ (j : ℕ)) *ᵥ v)ᵀ

private theorem omega_pow_injective {ω : Fˣ} (hω : ω ≠ 1) (hω3 : ω ^ 3 = 1) :
    Function.Injective fun j : Fin 3 => (ω : F) ^ (j : ℕ) := by
  have h1 := omega_sq_add ω hω hω3
  have hω1 : (ω : F) ≠ 1 := fun h => hω (Units.ext (by simpa using h))
  have hω0 : (ω : F) ≠ 0 := ω.ne_zero
  have h2 : (ω : F) ^ 2 ≠ 1 := by
    have h3' : (ω : F) ^ 3 = 1 := by simpa using congrArg Units.val hω3
    intro h; apply hω1; linear_combination h3' - (ω : F) * h
  have h3 : (ω : F) ^ 2 ≠ ω := by
    intro h; apply hω1
    have : (ω : F) * (ω - 1) = 0 := by linear_combination h
    simpa [hω0, sub_eq_zero] using this
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

private theorem isUnit_colMat {a b : GL (Fin 3) F} {ω : Fˣ} (hω : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    (hab : a * b * a⁻¹ * b⁻¹ = sc ω) {v : Fin 3 → F} (hv0 : v ≠ 0)
    (hav : (a : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v) :
    IsUnit (colMat (b : Matrix (Fin 3) (Fin 3) F) v) := by
  rw [← Matrix.linearIndependent_cols_iff_isUnit]
  refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' (a : Matrix (Fin 3) (Fin 3) F))
    _ (omega_pow_injective hω hω3) _ fun j => ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact mulVec_pow_eigen (mul_eq_smul_of_commutator hab) hav j
  · intro h
    apply hv0
    have h' : ((b ^ (j : ℕ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = 0 := by
      rw [Units.val_pow_eq_pow_val]; exact h
    have := congrArg (fun w => ((b ^ (j : ℕ))⁻¹ : GL (Fin 3) F).val *ᵥ w) h'
    simpa [Matrix.mulVec_mulVec] using this

private theorem colMat_apply (B : Matrix (Fin 3) (Fin 3) F) (v : Fin 3 → F) (i j : Fin 3) :
    colMat B v i j = ((B ^ (j : ℕ)) *ᵥ v) i := rfl

private theorem mul_apply_eq_mulVec (M Q : Matrix (Fin 3) (Fin 3) F) (i j : Fin 3) :
    (M * Q) i j = (M *ᵥ fun k => Q k j) i := by
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

private theorem coe_diagOmega (ω : Fˣ) :
    ((diagOmega ω : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal fun j : Fin 3 => (ω : F) ^ (j : ℕ) := by
  change diagonal _ = _
  congr 1; funext j; fin_cases j <;> simp

private theorem mul_colMat_diag {M B : Matrix (Fin 3) (Fin 3) F} {ω : F}
    (hMB : M * B = ω • (B * M)) {v : Fin 3 → F} (hv : M *ᵥ v = v) :
    M * colMat B v = colMat B v * diagonal fun j : Fin 3 => ω ^ (j : ℕ) := by
  ext i j
  rw [mul_apply_eq_mulVec, Matrix.mul_diagonal]
  change (M *ᵥ ((B ^ (j : ℕ)) *ᵥ v)) i = _
  rw [mulVec_pow_eigen hMB hv j, colMat_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

private theorem mul_colMat_cyc {B : Matrix (Fin 3) (Fin 3) F} {μ : F} (hB3 : B ^ 3 = μ • 1)
    (v : Fin 3 → F) : B * colMat B v = colMat B v * cycMatrix μ := by
  have h3 : B *ᵥ ((B ^ 2) *ᵥ v) = μ • v := by
    rw [Matrix.mulVec_mulVec, ← pow_succ', hB3, Matrix.smul_mulVec, Matrix.one_mulVec]
  ext i j
  rw [mul_apply_eq_mulVec]
  fin_cases j
  · simp [colMat_apply, Matrix.mul_apply, Fin.sum_univ_three, cycMatrix]
  · simp [colMat_apply, Matrix.mul_apply, Fin.sum_univ_three, cycMatrix, Matrix.mulVec_mulVec,
      pow_two]
  · change (B *ᵥ ((B ^ 2) *ᵥ v)) i = _
    rw [h3]
    simp [colMat_apply, Matrix.mul_apply, Fin.sum_univ_three, cycMatrix, mul_comm]

private theorem exists_conj_of_eigen {a b : GL (Fin 3) F} {ω μ : Fˣ} (hω : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    (hab : a * b * a⁻¹ * b⁻¹ = sc ω) (hb3 : b ^ 3 = sc μ) {v : Fin 3 → F} (hv0 : v ≠ 0)
    (hav : (a : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v) :
    ∃ P : GL (Fin 3) F, P * a * P⁻¹ = diagOmega ω ∧ P * b * P⁻¹ = cycMat μ := by
  obtain ⟨Q, hQ⟩ := isUnit_colMat hω hω3 hab hv0 hav
  have hB3 : (b : Matrix (Fin 3) (Fin 3) F) ^ 3 = (μ : F) • 1 := by
    rw [← Units.val_pow_eq_pow_val, hb3, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← mul_one (diagonal _), ← Matrix.smul_eq_diagonal_mul]
  refine ⟨Q⁻¹, ?_, ?_⟩
  · rw [inv_inv, mul_assoc, inv_mul_eq_iff_eq_mul]
    ext : 1
    rw [Units.val_mul, Units.val_mul, hQ, coe_diagOmega]
    exact mul_colMat_diag (mul_eq_smul_of_commutator hab) hav
  · rw [inv_inv, mul_assoc, inv_mul_eq_iff_eq_mul]
    ext : 1
    rw [Units.val_mul, Units.val_mul, hQ]
    exact mul_colMat_cyc hB3 v

private theorem ne_one_of_commutator {g h : GL (Fin 3) F} {ω : Fˣ} (hω : g * h * g⁻¹ * h⁻¹ = sc ω)
    (hgh : g * h ≠ h * g) : ω ≠ 1 := by
  rintro rfl
  exact hgh (commutatorElement_eq_one_iff_mul_comm.mp (by rw [commutatorElement_def, hω, map_one]))

private theorem cube_mul_mem {A : Subgroup (GL (Fin 3) F)} (hA : IsElemModScalars 3 A)
    {x y : GL (Fin 3) F} (hx : x ∈ A) (hy : y ∈ A) : (x * y) ^ 3 = y ^ 3 * x ^ 3 := by
  have hc := hA.commutator_mem x hx y hy
  obtain ⟨ω, hω, hω3⟩ := commutator_scalar hc
  refine mul_pow_three_of_comm hc (by group) ?_
  rw [hω, ← map_pow, hω3, map_one]

private theorem mul_pow_ne {g h : GL (Fin 3) F} (hgh : g * h ≠ h * g) (n : ℕ) :
    g * h ^ n * h ≠ h * (g * h ^ n) := by
  intro heq
  apply hgh
  refine mul_right_cancel (b := h ^ n) ?_
  calc g * h * h ^ n = g * h ^ n * h := by rw [mul_assoc, mul_assoc, pow_mul_comm']
    _ = h * (g * h ^ n) := heq
    _ = h * g * h ^ n := (mul_assoc _ _ _).symm

private theorem exists_cube_elt [Finite F] {A : Subgroup (GL (Fin 3) F)} (hA : IsElemModScalars 3 A)
    {g h : GL (Fin 3) F} (hg : g ∈ A) (hh : h ∈ A) (hgh : g * h ≠ h * g) :
    ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x ∧ ∃ κ : Fˣ, x ^ 3 = sc (κ ^ 3) := by
  obtain ⟨l, hl⟩ := exists_scalar_of_mem_center (hA.pow_mem g hg)
  obtain ⟨m, hm⟩ := exists_scalar_of_mem_center (hA.pow_mem h hh)
  by_cases hcl : ∃ k : Fˣ, k ^ 3 = l
  · obtain ⟨k, rfl⟩ := hcl
    exact ⟨g, hg, h, hh, hgh, k, hl⟩
  by_cases hcm : ∃ k : Fˣ, k ^ 3 = m
  · obtain ⟨k, rfl⟩ := hcm
    exact ⟨h, hh, g, hg, Ne.symm hgh, k, hm⟩
  have key : ∀ n : ℕ, ∀ k : Fˣ, k ^ 3 = l * m ^ n →
      ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x ∧ ∃ κ : Fˣ, x ^ 3 = sc (κ ^ 3) := by
    intro n k hk
    refine ⟨g * h ^ n, A.mul_mem hg (A.pow_mem hh n), h, hh, mul_pow_ne hgh n, k, ?_⟩
    rw [cube_mul_mem hA hg (A.pow_mem hh n), ← pow_mul, mul_comm n 3, pow_mul, hm, hl, ← map_pow,
      ← map_mul, hk, mul_comm]
  rcases cube_dichotomy_units hcl hcm with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact key 1 k (by rw [pow_one]; exact hk)
  · exact key 2 k hk

private theorem eq_three_of_noncomm {p : ℕ} (hp : p.Prime) {A : Subgroup (GL (Fin 3) F)}
    (hA : IsElemModScalars p A) {g h : GL (Fin 3) F} (hg : g ∈ A) (hh : h ∈ A)
    (hgh : g * h ≠ h * g) : p = 3 ∧ ∃ ω : Fˣ, orderOf ω = 3 := by
  have hc := hA.commutator_mem g hg h hh
  obtain ⟨ω, hω, hω3⟩ := commutator_scalar hc
  have hω1 := ne_one_of_commutator hω hgh
  have hωp : ω ^ p = 1 := by
    have h1 := conj_pow_eq hc (show g * h * g⁻¹ = (g * h * g⁻¹ * h⁻¹) * h by group) p
    rw [← Subgroup.mem_center_iff.mp (hA.pow_mem g hg) h, mul_inv_cancel_right, hω,
      ← map_pow] at h1
    apply scalar_injective
    rw [map_one]
    exact (mul_right_cancel (h1.symm.trans (one_mul h).symm))
  have hord3 : orderOf ω = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hω3) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hω1
    · exact h1
  refine ⟨((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
    (hord3 ▸ orderOf_dvd_of_pow_eq_one hωp)).symm, ω, hord3⟩

private theorem exists_eigen_pair [Finite F] {A : Subgroup (GL (Fin 3) F)}
    (hA : IsElemModScalars 3 A) {g h : GL (Fin 3) F} (hg : g ∈ A) (hh : h ∈ A)
    (hgh : g * h ≠ h * g) :
    ∃ a ∈ A, ∃ b ∈ A, a * b ≠ b * a ∧ ∃ v : Fin 3 → F, v ≠ 0 ∧
      (a : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v := by
  obtain ⟨ζ, hζ, hζ3⟩ := commutator_scalar (hA.commutator_mem g hg h hh)
  have hζ1 := ne_one_of_commutator hζ hgh
  obtain ⟨x, hx, y, hy, hxy, κ, hx3⟩ := exists_cube_elt hA hg hh hgh
  obtain ⟨β, v, hv0, hxv⟩ := exists_eigen_of_pow_three hζ1 hζ3 hx3
  have hcen := Subgroup.mem_center_iff.mp (scalar_mem_center (F := F) β⁻¹) y
  refine ⟨sc β⁻¹ * x, A.mul_mem (hA.center_le (scalar_mem_center _)) hx, y, hy, ?_, v, hv0, ?_⟩
  · intro heq
    apply hxy
    apply mul_left_cancel (a := sc β⁻¹)
    rw [← mul_assoc, heq, ← mul_assoc, hcen, mul_assoc]
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hxv, Matrix.mulVec_smul,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    ext i
    simp

theorem exists_conj_normalForm {q : ℕ} [Fact q.Prime] (_hq2 : q ≠ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ≠ q) {A : Subgroup (GL (Fin 3) (ZMod q))} (hA : IsElemModScalars p A)
    (hnc : ∃ g ∈ A, ∃ h ∈ A, g * h ≠ h * g) :
    p = 3 ∧ q % 3 = 1 ∧ ∃ (ω μ : (ZMod q)ˣ) (P : GL (Fin 3) (ZMod q)), ω ≠ 1 ∧ ω ^ 3 = 1 ∧
      diagOmega ω ∈ A.map (MulAut.conj P).toMonoidHom ∧
      cycMat μ ∈ A.map (MulAut.conj P).toMonoidHom := by
  obtain ⟨g, hg, h, hh, hgh⟩ := hnc
  obtain ⟨rfl, ω₀, hord⟩ := eq_three_of_noncomm hp hA hg hh hgh
  have hq3 : q % 3 = 1 := by
    have hd := orderOf_dvd_card (x := ω₀)
    rw [hord, ZMod.card_units] at hd
    have := (Fact.out : q.Prime).two_le
    omega
  obtain ⟨a, ha, b, hb, hab, v, hv0, hav⟩ := exists_eigen_pair hA hg hh hgh
  obtain ⟨ω, hω, hω3⟩ := commutator_scalar (hA.commutator_mem a ha b hb)
  obtain ⟨μ, hμ⟩ := exists_scalar_of_mem_center (hA.pow_mem b hb)
  have hω1 := ne_one_of_commutator hω hab
  obtain ⟨P, hPa, hPb⟩ := exists_conj_of_eigen hω1 hω3 hω hμ hv0 hav
  exact ⟨rfl, hq3, ω, μ, P, hω1, hω3, Subgroup.mem_map.mpr ⟨a, ha, hPa⟩,
    Subgroup.mem_map.mpr ⟨b, hb, hPb⟩⟩

theorem exists_conj_cycMat_one {F : Type} [Field F] {A : Subgroup (GL (Fin 3) F)}
    (hZ : Subgroup.center (GL (Fin 3) F) ≤ A) {ω ν : Fˣ} (ha : diagOmega ω ∈ A)
    (hb : cycMat (ν ^ 3) ∈ A) :
    ∃ P : GL (Fin 3) F, diagOmega ω ∈ A.map (MulAut.conj P).toMonoidHom ∧
      cycMat 1 ∈ A.map (MulAut.conj P).toMonoidHom := by
  refine ⟨diagThree ![1, ν, ν ^ 2], Subgroup.mem_map.mpr ⟨diagOmega ω, ha, ?_⟩,
    Subgroup.mem_map.mpr ⟨sc ν⁻¹ * cycMat (ν ^ 3), A.mul_mem (hZ (scalar_mem_center _)) hb, ?_⟩⟩
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [mul_inv_eq_iff_eq_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagOmega, diagThree, mul_comm]
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [mul_inv_eq_iff_eq_mul]
    ext i j
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    fin_cases i <;> fin_cases j <;>
      simp [diagThree, cycMat, cycMatrix, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
