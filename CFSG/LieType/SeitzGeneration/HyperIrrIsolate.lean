module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import CFSG.LieType.SeitzGeneration.HyperIrrKron
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix Finset

variable {F : Type*} [Field F] {p : ℕ}

@[expose] def diagUpd (m : Fin p) (x : F) : Matrix (Fin p) (Fin p) F :=
  Matrix.diagonal fun i => if i = m then x else 1

theorem diagUpd_mul_inv (m : Fin p) {x : F} (hx : x ≠ 0) :
    diagUpd m x * diagUpd m x⁻¹ = (1 : Matrix (Fin p) (Fin p) F) := by
  rw [diagUpd, diagUpd, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases h : i = m <;> simp [h, hx]

theorem det_diagUpd (m : Fin p) (x : F) : (diagUpd m x).det = x := by
  simp [diagUpd, Matrix.det_diagonal, Finset.prod_ite_eq']

@[expose] noncomputable def tEl (m : Fin p) (x : F) (hx : x ^ p = 1) :
    SpecialLinearGroup (Fin (p * p)) F :=
  ⟨kr (diagUpd m x) 1, by rw [det_kr, det_diagUpd, Matrix.det_one, one_pow, mul_one, hx]⟩

theorem coe_tEl (m : Fin p) (x : F) (hx : x ^ p = 1) :
    ((tEl m x hx : SpecialLinearGroup (Fin (p * p)) F) : Matrix (Fin (p * p)) (Fin (p * p)) F) =
      kr (diagUpd m x) 1 := rfl

@[expose] def nilSub (K' : Subgroup (SpecialLinearGroup (Fin (p * p)) F)) (j l : Fin p)
    (hjl : j ≠ l) : Submodule F (Matrix (Fin p) (Fin p) F) where
  carrier := {A | ∀ c : F, ∃ h ∈ K', (h : Matrix (Fin (p * p)) (Fin (p * p)) F) =
    1 + c • kr A (Matrix.single j l 1)}
  zero_mem' := fun c => ⟨1, K'.one_mem, by simp [kr_zero_left]⟩
  smul_mem' := fun μ A hA c => by
    obtain ⟨h, hh, he⟩ := hA (c * μ)
    exact ⟨h, hh, by rw [he, kr_smul_left, smul_smul]⟩
  add_mem' := fun {A B} hA hB c => by
    obtain ⟨h, hh, he⟩ := hA c
    obtain ⟨h', hh', he'⟩ := hB c
    refine ⟨h * h', K'.mul_mem hh hh', ?_⟩
    have hEE : (Matrix.single j l (1 : F)) * Matrix.single j l 1 = 0 :=
      Matrix.single_mul_single_of_ne 1 j l j hjl.symm 1
    have h2 : kr A (Matrix.single j l 1) * kr B (Matrix.single j l 1) = 0 := by
      rw [kr_mul, hEE, kr_zero_right]
    rw [Matrix.SpecialLinearGroup.coe_mul, he, he', kr_add_left]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, h2, smul_zero, add_zero, smul_add]
    abel

theorem nilSub_ad {K' : Subgroup (SpecialLinearGroup (Fin (p * p)) F)} {j l : Fin p}
    {hjl : j ≠ l} (m : Fin p) {x : F} (hx : x ^ p = 1) (hx' : x⁻¹ ^ p = 1)
    (hxK : tEl m x hx ∈ K') (hxK' : tEl m x⁻¹ hx' ∈ K') {A : Matrix (Fin p) (Fin p) F}
    (hA : A ∈ nilSub K' j l hjl) : diagUpd m x * A * diagUpd m x⁻¹ ∈ nilSub K' j l hjl := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · exact absurd (Fin.pos_iff_nonempty.2 ⟨m⟩) (by simp)
    · rw [zero_pow hp.ne'] at hx; exact zero_ne_one hx
  intro c
  obtain ⟨h, hh, he⟩ := hA c
  refine ⟨tEl m x hx * h * tEl m x⁻¹ hx', K'.mul_mem (K'.mul_mem hxK hh) hxK', ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, he, coe_tEl,
    coe_tEl]
  have h1 : kr (diagUpd m x) 1 * kr (diagUpd m x⁻¹) 1 = (1 : Matrix (Fin (p * p)) _ F) := by
    rw [kr_mul, diagUpd_mul_inv m hx0, Matrix.one_mul, kr_one]
  have h2 : kr (diagUpd m x) 1 * kr A (Matrix.single j l 1) * kr (diagUpd m x⁻¹) 1 =
      kr (diagUpd m x * A * diagUpd m x⁻¹) (Matrix.single j l 1) := by
    rw [kr_mul, kr_mul]; simp
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
    h1, h2]

end CFSG.LieType.SeitzGeneration

namespace CFSG.LieType.SeitzGeneration

open Matrix Finset

variable {F : Type*} [Field F] {p : ℕ}

theorem geom_sum_root_eq_zero {y : F} (hy : y ^ p = 1) (hy1 : y ≠ 1) :
    ∑ t ∈ range p, y ^ t = 0 := by
  have h := geom_sum_mul y p
  rw [hy, sub_self] at h
  exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hy1)

@[expose] def rowPart (m : Fin p) (A : Matrix (Fin p) (Fin p) F) : Matrix (Fin p) (Fin p) F :=
  Matrix.of fun i k => if i = m ∧ k ≠ m then A i k else 0

@[expose] def colPart (k₀ : Fin p) (A : Matrix (Fin p) (Fin p) F) : Matrix (Fin p) (Fin p) F :=
  Matrix.of fun i k => if k = k₀ ∧ i ≠ k₀ then A i k else 0

theorem diag_conj_apply (m : Fin p) (x y : F) (A : Matrix (Fin p) (Fin p) F) (i k : Fin p) :
    (diagUpd m x * A * diagUpd m y) i k =
      (if i = m then x else 1) * A i k * (if k = m then y else 1) := by
  simp [diagUpd, Matrix.diagonal_mul, Matrix.mul_diagonal]

variable {ω : F}

theorem root_sq_ne_one (hω : IsPrimitiveRoot ω p) (hp3 : 3 ≤ p) : ω ^ 2 ≠ 1 := fun h =>
  absurd (Nat.le_of_dvd (by norm_num) ((hω.pow_eq_one_iff_dvd 2).1 h)) (by omega)

theorem row_extract (hω : IsPrimitiveRoot ω p) (hp3 : 3 ≤ p) (m : Fin p)
    (A : Matrix (Fin p) (Fin p) F) :
    ∑ t ∈ range p, (ω⁻¹ ^ t) • (diagUpd m (ω ^ t) * A * diagUpd m (ω ^ t)⁻¹) =
      (p : F) • rowPart m A := by
  have hω0 : ω ≠ 0 := hω.ne_zero (by omega)
  have hωp : ω ^ p = 1 := hω.pow_eq_one
  have hω1 : ω ≠ 1 := hω.ne_one (by omega)
  have hy : ω⁻¹ ^ p = 1 := by rw [inv_pow, hωp, inv_one]
  have hy1 : ω⁻¹ ≠ 1 := fun h => hω1 (inv_eq_one.1 h)
  have hy2 : (ω⁻¹ ^ 2) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]
  have hy21 : ω⁻¹ ^ 2 ≠ 1 := fun h => root_sq_ne_one hω hp3 (by
    rw [inv_pow, inv_eq_one] at h; exact h)
  ext i k
  simp only [Matrix.sum_apply, Matrix.smul_apply, diag_conj_apply, rowPart, Matrix.of_apply,
    smul_eq_mul]
  by_cases hi : i = m <;> by_cases hk : k = m
  · have h1 : ∀ t : ℕ, ω⁻¹ ^ t * ((if i = m then ω ^ t else 1) * A i k *
        (if k = m then (ω ^ t)⁻¹ else 1)) = ω⁻¹ ^ t * A i k := fun t => by
      simp only [hi, hk, ite_true]; rw [inv_pow]; field_simp
    simp only [h1, ← Finset.sum_mul, geom_sum_root_eq_zero hy hy1, zero_mul]
    simp [hk]
  · have h1 : ∀ t : ℕ, ω⁻¹ ^ t * ((if i = m then ω ^ t else 1) * A i k *
        (if k = m then (ω ^ t)⁻¹ else 1)) = A i k := fun t => by
      simp only [hi, hk, ite_true, ite_false]; rw [mul_one, ← mul_assoc, ← mul_pow,
        inv_mul_cancel₀ hω0, one_pow, one_mul]
    simp only [h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    simp [hi, hk]
  · have h1 : ∀ t : ℕ, ω⁻¹ ^ t * ((if i = m then ω ^ t else 1) * A i k *
        (if k = m then (ω ^ t)⁻¹ else 1)) = (ω⁻¹ ^ 2) ^ t * A i k := fun t => by
      simp only [hi, hk, ite_true, ite_false]
      have h2 : (ω⁻¹ ^ 2) ^ t = ω⁻¹ ^ t * ω⁻¹ ^ t := by rw [← pow_mul, mul_comm, pow_mul, sq]
      rw [h2]; simp only [inv_pow]; field_simp
    simp only [h1, ← Finset.sum_mul, geom_sum_root_eq_zero hy2 hy21, zero_mul]
    simp [hi]
  · have h1 : ∀ t : ℕ, ω⁻¹ ^ t * ((if i = m then ω ^ t else 1) * A i k *
        (if k = m then (ω ^ t)⁻¹ else 1)) = ω⁻¹ ^ t * A i k := fun t => by
      simp only [hi, hk, ite_false, one_mul, mul_one]
    simp only [h1, ← Finset.sum_mul, geom_sum_root_eq_zero hy hy1, zero_mul]
    simp [hi]

theorem col_extract (hω : IsPrimitiveRoot ω p) (hp3 : 3 ≤ p) (k₀ : Fin p)
    (A : Matrix (Fin p) (Fin p) F) :
    ∑ t ∈ range p, (ω ^ t) • (diagUpd k₀ (ω ^ t) * A * diagUpd k₀ (ω ^ t)⁻¹) =
      (p : F) • colPart k₀ A := by
  have hω0 : ω ≠ 0 := hω.ne_zero (by omega)
  have hωp : ω ^ p = 1 := hω.pow_eq_one
  have hω1 : ω ≠ 1 := hω.ne_one (by omega)
  have hy2 : (ω ^ 2) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hωp, one_pow]
  have hy21 : ω ^ 2 ≠ 1 := root_sq_ne_one hω hp3
  ext i k
  simp only [Matrix.sum_apply, Matrix.smul_apply, diag_conj_apply, colPart, Matrix.of_apply,
    smul_eq_mul]
  by_cases hi : i = k₀ <;> by_cases hk : k = k₀
  · have h1 : ∀ t : ℕ, ω ^ t * ((if i = k₀ then ω ^ t else 1) * A i k *
        (if k = k₀ then (ω ^ t)⁻¹ else 1)) = ω ^ t * A i k := fun t => by
      simp only [hi, hk, ite_true]; field_simp
    simp only [h1, ← Finset.sum_mul, geom_sum_root_eq_zero hωp hω1, zero_mul]
    simp [hi]
  · have h1 : ∀ t : ℕ, ω ^ t * ((if i = k₀ then ω ^ t else 1) * A i k *
        (if k = k₀ then (ω ^ t)⁻¹ else 1)) = (ω ^ 2) ^ t * A i k := fun t => by
      simp only [hi, hk, ite_true, ite_false]
      have h2 : (ω ^ 2) ^ t = ω ^ t * ω ^ t := by rw [← pow_mul, mul_comm, pow_mul, sq]
      rw [h2]; ring
    simp only [h1, ← Finset.sum_mul, geom_sum_root_eq_zero hy2 hy21, zero_mul]
    simp [hk]
  · have h1 : ∀ t : ℕ, ω ^ t * ((if i = k₀ then ω ^ t else 1) * A i k *
        (if k = k₀ then (ω ^ t)⁻¹ else 1)) = A i k := fun t => by
      simp only [hi, hk, ite_true, ite_false]; field_simp
    simp only [h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    simp [hi, hk]
  · have h1 : ∀ t : ℕ, ω ^ t * ((if i = k₀ then ω ^ t else 1) * A i k *
        (if k = k₀ then (ω ^ t)⁻¹ else 1)) = ω ^ t * A i k := fun t => by
      simp only [hi, hk, ite_false, one_mul, mul_one]
    simp only [h1, ← Finset.sum_mul, geom_sum_root_eq_zero hωp hω1, zero_mul]
    simp [hk]

section Closure

variable {K' : Subgroup (SpecialLinearGroup (Fin (p * p)) F)} {j l : Fin p} {hjl : j ≠ l}

theorem rowPart_mem_nilSub (hω : IsPrimitiveRoot ω p) (hp3 : 3 ≤ p) (hpF : (p : F) ≠ 0)
    (ht : ∀ (m : Fin p) (x : F) (hx : x ^ p = 1), tEl m x hx ∈ K') (m : Fin p)
    {A : Matrix (Fin p) (Fin p) F} (hA : A ∈ nilSub K' j l hjl) :
    rowPart m A ∈ nilSub K' j l hjl := by
  have hωp : ω ^ p = 1 := hω.pow_eq_one
  have h1 : rowPart m A = ((p : F)⁻¹) • ∑ t ∈ range p, (ω⁻¹ ^ t) •
      (diagUpd m (ω ^ t) * A * diagUpd m (ω ^ t)⁻¹) := by
    rw [row_extract hω hp3 m A, smul_smul, inv_mul_cancel₀ hpF, one_smul]
  rw [h1]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ ?_)
  have hx : (ω ^ t) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hωp, one_pow]
  have hx' : ((ω ^ t)⁻¹) ^ p = 1 := by rw [inv_pow, hx, inv_one]
  exact nilSub_ad m hx hx' (ht m _ hx) (ht m _ hx') hA

theorem colPart_mem_nilSub (hω : IsPrimitiveRoot ω p) (hp3 : 3 ≤ p) (hpF : (p : F) ≠ 0)
    (ht : ∀ (m : Fin p) (x : F) (hx : x ^ p = 1), tEl m x hx ∈ K') (k₀ : Fin p)
    {A : Matrix (Fin p) (Fin p) F} (hA : A ∈ nilSub K' j l hjl) :
    colPart k₀ A ∈ nilSub K' j l hjl := by
  have hωp : ω ^ p = 1 := hω.pow_eq_one
  have h1 : colPart k₀ A = ((p : F)⁻¹) • ∑ t ∈ range p, (ω ^ t) •
      (diagUpd k₀ (ω ^ t) * A * diagUpd k₀ (ω ^ t)⁻¹) := by
    rw [col_extract hω hp3 k₀ A, smul_smul, inv_mul_cancel₀ hpF, one_smul]
  rw [h1]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ ?_)
  have hx : (ω ^ t) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hωp, one_pow]
  have hx' : ((ω ^ t)⁻¹) ^ p = 1 := by rw [inv_pow, hx, inv_one]
  exact nilSub_ad k₀ hx hx' (ht k₀ _ hx) (ht k₀ _ hx') hA

theorem single_mem_nilSub (hω : IsPrimitiveRoot ω p) (hp3 : 3 ≤ p) (hpF : (p : F) ≠ 0)
    (ht : ∀ (m : Fin p) (x : F) (hx : x ^ p = 1), tEl m x hx ∈ K')
    (hP : (projF : Matrix (Fin p) (Fin p) F) ∈ nilSub K' j l hjl) {m k₀ : Fin p} (hmk : m ≠ k₀) :
    (Matrix.single m k₀ (1 : F)) ∈ nilSub K' j l hjl := by
  have h1 := colPart_mem_nilSub hω hp3 hpF ht k₀ (rowPart_mem_nilSub hω hp3 hpF ht m hP)
  have h2 : colPart k₀ (rowPart m (projF : Matrix (Fin p) (Fin p) F)) =
      (p : F)⁻¹ • Matrix.single m k₀ (1 : F) := by
    ext i k
    simp only [colPart, rowPart, projF, onesM, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.single_apply, mul_ite, mul_one, mul_zero]
    by_cases hi : i = m <;> by_cases hk : k = k₀
    · subst hi; subst hk; simp [hmk, hmk.symm]
    · have hk' : ¬k₀ = k := fun h => hk h.symm
      simp [hk, hk']
    · have hi' : ¬m = i := fun h => hi h.symm
      subst hk; simp [hi, hi', hmk.symm]
    · have hk' : ¬k₀ = k := fun h => hk h.symm
      simp [hk, hk']
  rw [h2] at h1
  have h3 := Submodule.smul_mem _ (p : F) h1
  rwa [smul_smul, mul_inv_cancel₀ hpF, one_smul] at h3

end Closure

end CFSG.LieType.SeitzGeneration
