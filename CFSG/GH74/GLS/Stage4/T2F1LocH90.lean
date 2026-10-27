module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace CFSG.GH74.GLS.Stage4.Rest.F1Loc

private theorem pow_succ_apply {F : Type} [Field F] (σ : F ≃+* F) (n : ℕ) (z : F) :
    (σ ^ (n + 1)) z = σ ((σ ^ n) z) := by
  rw [pow_succ']
  rfl

private theorem mul_apply_prod_range {F : Type} [Field F] (σ : F ≃+* F) (x : F) (i : ℕ) :
    x * σ (∏ j ∈ Finset.range i, (σ ^ j) x) = ∏ j ∈ Finset.range (i + 1), (σ ^ j) x := by
  rw [Finset.prod_range_succ', map_prod, mul_comm]
  simp [pow_succ_apply]

theorem hilbert90_finiteField {F : Type} [Field F] [Finite F] (σ : F ≃+* F) {r : ℕ}
    (hr : orderOf σ = r) {x : F} (hx : ∏ i ∈ Finset.range r, (σ ^ i) x = 1) :
    ∃ y : F, y ≠ 0 ∧ x * σ y = y := by
  have : Finite (F ≃+* F) :=
    Finite.of_injective (fun τ : F ≃+* F => (τ : F → F)) DFunLike.coe_injective
  have hr0 : 0 < r := hr ▸ orderOf_pos_iff.mpr (isOfFinOrder_of_finite σ)
  have hσr : σ ^ r = 1 := hr ▸ pow_orderOf_eq_one σ
  let a : ℕ → F := fun i => ∏ j ∈ Finset.range i, (σ ^ j) x
  let T : F → F := fun c => ∑ i ∈ Finset.range r, a i * (σ ^ i) c
  have hfix : ∀ c, x * σ (T c) = T c := by
    intro c
    let f : ℕ → F := fun i => a i * (σ ^ i) c
    have hstep : x * σ (T c) = ∑ i ∈ Finset.range r, f (i + 1) := by
      simp only [T, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ← mul_assoc, mul_apply_prod_range σ x i]
      exact congrArg (fun t => (∏ j ∈ Finset.range (i + 1), (σ ^ j) x) * t)
        (pow_succ_apply σ i c).symm
    have hfr : f r = f 0 := by
      show a r * (σ ^ r) c = a 0 * (σ ^ 0) c
      rw [show a r = 1 from hx, hσr]
      simp [a]
    have h3 : ∑ i ∈ Finset.range r, f (i + 1) = ∑ i ∈ Finset.range r, f i := by
      have := (Finset.sum_range_succ' f r).symm.trans (Finset.sum_range_succ f r)
      rw [hfr] at this
      exact add_right_cancel this
    rw [hstep, h3]
  have hne : ∃ c, T c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    let φ : Fin r → (F →* F) := fun i => ((σ ^ (i : ℕ) : F ≃+* F) : F →* F)
    have hφ : Function.Injective φ := by
      intro i j hij
      have h2 : σ ^ (i : ℕ) = σ ^ (j : ℕ) := by
        ext y
        exact DFunLike.congr_fun hij y
      exact Fin.ext
        (pow_injOn_Iio_orderOf (x := σ) (by rw [hr]; exact i.2) (by rw [hr]; exact j.2) h2)
    have hli := (linearIndependent_monoidHom F F).comp φ hφ
    have key := Fintype.linearIndependent_iff.mp hli (fun i : Fin r => a (i : ℕ)) (by
      funext c
      have h1 := hcon c
      simp only [T] at h1
      rw [Finset.sum_range (fun i => a i * (σ ^ i) c)] at h1
      simpa [φ] using h1) ⟨0, hr0⟩
    simp [a] at key
  obtain ⟨c, hc⟩ := hne
  exact ⟨T c, hc, hfix c⟩

theorem exists_fixed_smul_of_semilinear {F : Type} [Field F] [Finite F] (σ : F ≃+* F) {r : ℕ}
    (hr : orderOf σ = r) (g : Matrix (Fin 2) (Fin 2) F) (hg : g.det ≠ 0) (c : F)
    (hc : g.map σ = c • g) : ∃ ν : F, ν ≠ 0 ∧ (ν • g).map σ = ν • g := by
  have hσr : σ ^ r = 1 := hr ▸ pow_orderOf_eq_one σ
  have hent : ∀ i j, σ (g i j) = c * g i j := fun i j => congrFun (congrFun hc i) j
  have hpow : ∀ (k : ℕ) (i j : Fin 2),
      (σ ^ k) (g i j) = (∏ m ∈ Finset.range k, (σ ^ m) c) * g i j := by
    intro k i j
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_range_succ, pow_succ]
      show (σ ^ k) (σ (g i j)) = _
      rw [hent, map_mul, ih]
      ring
  have hprod : ∏ m ∈ Finset.range r, (σ ^ m) c = 1 := by
    by_contra hne
    apply hg
    have h0 : ∀ i j, g i j = 0 := by
      intro i j
      have h := hpow r i j
      rw [hσr] at h
      have h' : (∏ m ∈ Finset.range r, (σ ^ m) c - 1) * g i j = 0 := by
        rw [sub_mul, ← h]
        simp
      exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hne)
    rw [Matrix.det_fin_two, h0 0 0, h0 0 1, h0 1 0, h0 1 1]
    simp
  obtain ⟨y, hy0, hy⟩ := hilbert90_finiteField σ hr hprod
  refine ⟨y, hy0, ?_⟩
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  rw [map_mul, hent, ← mul_assoc, mul_comm (σ y) c, hy]

end CFSG.GH74.GLS.Stage4.Rest.F1Loc
