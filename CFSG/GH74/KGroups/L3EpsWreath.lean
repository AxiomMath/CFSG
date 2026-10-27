module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.GH74.KGroups.L3Eps

@[expose] def WrPres (R : Type*) [Group R] (s : ℕ) : Prop :=
  ∃ u v τ : R, Commute u v ∧ u ^ s = 1 ∧ v ^ s = 1 ∧ τ ^ 2 = 1 ∧ τ⁻¹ * u * τ = v ∧
    (∀ a b : ℕ, u ^ a * v ^ b = 1 → s ∣ a ∧ s ∣ b) ∧
    ∀ w : R, ∃ i j e : ℕ, e < 2 ∧ w = u ^ i * v ^ j * τ ^ e

theorem WrPres.congr {R R' : Type*} [Group R] [Group R'] {s : ℕ} (h : WrPres R s) (e : R ≃* R') :
    WrPres R' s := by
  obtain ⟨u, v, τ, huv, hus, hvs, hτ, hτu, hind, hnf⟩ := h
  refine ⟨e u, e v, e τ, huv.map e, ?_, ?_, ?_, ?_, ?_, fun w => ?_⟩
  · rw [← map_pow, hus, map_one]
  · rw [← map_pow, hvs, map_one]
  · rw [← map_pow, hτ, map_one]
  · rw [← map_inv, ← map_mul, ← map_mul, hτu]
  · intro a b hab
    apply hind a b
    apply e.injective
    rw [map_mul, map_pow, map_pow, hab, map_one]
  · obtain ⟨i, j, k, hk, hw⟩ := hnf (e.symm w)
    refine ⟨i, j, k, hk, ?_⟩
    apply e.symm.injective
    rw [hw, map_mul, map_mul, map_pow, map_pow, map_pow, MulEquiv.symm_apply_apply,
      MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

section Abstract

variable {R : Type*} [Group R]

theorem WrPres.exists_root {K : ℕ} (hK : 0 < K) (h : WrPres R (4 * K))
    (huniq : ∀ x y : R, (∀ r, x * r = r * x) → (∀ r, y * r = r * y) → x * x = 1 → y * y = 1 →
      x ≠ 1 → y ≠ 1 → x = y)
    {z : R} (hzc : ∀ r, z * r = r * z) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    {v₁ : R} (hv₁2 : v₁ * v₁ = 1) (hv₁1 : v₁ ≠ 1) (hv₁z : v₁ ≠ z)
    (hsq : (∃ u : R, u * u = 1 ∧ u ≠ 1 ∧ u ≠ z ∧ ∃ t, t * t = u) → ∃ t, t * t = v₁) :
    ∃ y : R, y ^ (2 * K) = v₁ := by
  obtain ⟨u, v, τ, huv, hus, hvs, hτ, hτu, hind, hnf⟩ := h
  have hττ : τ * τ = 1 := by rw [← sq]; exact hτ
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hττ
  rw [hτi] at hτu
  have hτv : τ * v * τ = u := by
    calc τ * v * τ = τ * (τ * u * τ) * τ := by rw [hτu]
      _ = (τ * τ) * u * (τ * τ) := by group
      _ = u := by rw [hττ]; group
  have hτpu : ∀ i : ℕ, τ * u ^ i * τ = v ^ i := by
    intro i
    have h1 : (τ * u * τ⁻¹) ^ i = τ * u ^ i * τ⁻¹ := conj_pow
    rw [hτi, hτu] at h1
    exact h1.symm
  have hτpv : ∀ j : ℕ, τ * v ^ j * τ = u ^ j := by
    intro j
    have h1 : (τ * v * τ⁻¹) ^ j = τ * v ^ j * τ⁻¹ := conj_pow
    rw [hτi, hτv] at h1
    exact h1.symm
  have hmulform : ∀ a b c d : ℕ, (u ^ a * v ^ b) * (u ^ c * v ^ d) = u ^ (a + c) * v ^ (b + d) := by
    intro a b c d
    rw [pow_add, pow_add]
    calc u ^ a * v ^ b * (u ^ c * v ^ d) = u ^ a * (v ^ b * u ^ c) * v ^ d := by group
      _ = u ^ a * (u ^ c * v ^ b) * v ^ d := by rw [← (huv.pow_pow c b).eq]
      _ = u ^ a * u ^ c * (v ^ b * v ^ d) := by group
  have hcent : ∀ a : ℕ, ∀ r : R, u ^ a * v ^ a * r = r * (u ^ a * v ^ a) := by
    intro a r
    obtain ⟨i, j, e, he, rfl⟩ := hnf r
    have c1 : Commute (u ^ a * v ^ a) (u ^ i) :=
      (Commute.pow_pow_self u a i).mul_left (huv.pow_pow i a).symm
    have c2 : Commute (u ^ a * v ^ a) (v ^ j) :=
      (huv.pow_pow a j).mul_left (Commute.pow_pow_self v a j)
    have c3 : Commute (u ^ a * v ^ a) τ := by
      have h1 : τ * (u ^ a * v ^ a) * τ = u ^ a * v ^ a := by
        calc τ * (u ^ a * v ^ a) * τ = (τ * u ^ a * τ) * (τ * v ^ a * τ) := by
              calc τ * (u ^ a * v ^ a) * τ = τ * u ^ a * (τ * τ) * v ^ a * τ := by
                    rw [hττ]; group
                _ = (τ * u ^ a * τ) * (τ * v ^ a * τ) := by group
          _ = v ^ a * u ^ a := by rw [hτpu, hτpv]
          _ = u ^ a * v ^ a := (huv.pow_pow a a).symm.eq
      calc u ^ a * v ^ a * τ = (τ * τ) * (u ^ a * v ^ a) * τ := by rw [hττ, one_mul]
        _ = τ * (τ * (u ^ a * v ^ a) * τ) := by group
        _ = τ * (u ^ a * v ^ a) := by rw [h1]
    exact ((c1.mul_right c2).mul_right (c3.pow_right e)).eq
  have hw₀c : ∀ r : R, u ^ (2 * K) * v ^ (2 * K) * r = r * (u ^ (2 * K) * v ^ (2 * K)) :=
    hcent (2 * K)
  have hw₀2 : u ^ (2 * K) * v ^ (2 * K) * (u ^ (2 * K) * v ^ (2 * K)) = 1 := by
    rw [hmulform, show 2 * K + 2 * K = 4 * K by ring, hus, hvs, one_mul]
  have hw₀1 : u ^ (2 * K) * v ^ (2 * K) ≠ 1 := by
    intro h
    have h1 := (hind _ _ h).1
    have := Nat.le_of_dvd (by omega) h1
    omega
  have hwz : u ^ (2 * K) * v ^ (2 * K) = z := huniq _ z hw₀c hzc hw₀2 hz2 hw₀1 hz1
  have hprem : ∃ u' : R, u' * u' = 1 ∧ u' ≠ 1 ∧ u' ≠ z ∧ ∃ t, t * t = u' := by
    refine ⟨u ^ (2 * K), ?_, ?_, ?_, u ^ K, ?_⟩
    · rw [← pow_add, show 2 * K + 2 * K = 4 * K by ring]
      exact hus
    · intro h
      have h1 := (hind (2 * K) 0 (by rw [h, pow_zero, mul_one])).1
      have := Nat.le_of_dvd (by omega) h1
      omega
    · intro h
      rw [← hwz] at h
      have h2 : u ^ (2 * K) * 1 = u ^ (2 * K) * v ^ (2 * K) := by rw [mul_one]; exact h
      have h3 : v ^ (2 * K) = 1 := (mul_left_cancel h2).symm
      have h1 := (hind 0 (2 * K) (by rw [pow_zero, one_mul]; exact h3)).2
      have := Nat.le_of_dvd (by omega) h1
      omega
    · rw [← pow_add]
      congr 1
      ring
  obtain ⟨t, ht⟩ := hsq hprem
  obtain ⟨i, j, e, he, rfl⟩ := hnf t
  have he' : e = 0 ∨ e = 1 := by omega
  rcases he' with rfl | rfl
  ·
    rw [pow_zero, mul_one] at ht
    rw [hmulform] at ht
    have hcases : ∀ x : R, x ^ (4 * K) = 1 → ∀ i : ℕ, K ∣ i →
        x ^ (i + i) = 1 ∨ x ^ (i + i) = x ^ (2 * K) := by
      intro x hx i ⟨i', hi'⟩
      obtain ⟨n, hn | hn⟩ := Nat.even_or_odd' i'
      · left
        have : i + i = 4 * K * n := by rw [hi', hn]; ring
        rw [this, pow_mul, hx, one_pow]
      · right
        have : i + i = 4 * K * n + 2 * K := by rw [hi', hn]; ring
        rw [this, pow_add, pow_mul, hx, one_pow, one_mul]
    have hv₁sq : u ^ (i + i + (i + i)) * v ^ (j + j + (j + j)) = 1 := by
      rw [← hmulform, ht]
      exact hv₁2
    obtain ⟨hi4, hj4⟩ := hind _ _ hv₁sq
    have hKi : K ∣ i := by
      have : 4 * K ∣ 4 * i := by rwa [show i + i + (i + i) = 4 * i by ring] at hi4
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    have hKj : K ∣ j := by
      have : 4 * K ∣ 4 * j := by rwa [show j + j + (j + j) = 4 * j by ring] at hj4
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    rcases hcases u hus i hKi with hA | hA <;> rcases hcases v hvs j hKj with hB | hB
    · exact absurd (by rw [← ht, hA, hB, one_mul]) hv₁1
    · exact ⟨v, by rw [← ht, hA, hB, one_mul]⟩
    · exact ⟨u, by rw [← ht, hA, hB, mul_one]⟩
    · exfalso
      apply hv₁z
      rw [← ht, hA, hB]
      exact hwz
  ·
    exfalso
    have h1 : τ * (u ^ i * v ^ j) * τ = v ^ i * u ^ j := by
      calc τ * (u ^ i * v ^ j) * τ = (τ * u ^ i * τ) * (τ * v ^ j * τ) := by
            calc τ * (u ^ i * v ^ j) * τ = τ * u ^ i * (τ * τ) * v ^ j * τ := by
                  rw [hττ]; group
              _ = (τ * u ^ i * τ) * (τ * v ^ j * τ) := by group
        _ = v ^ i * u ^ j := by rw [hτpu, hτpv]
    have h2 : u ^ i * v ^ j * τ ^ 1 * (u ^ i * v ^ j * τ ^ 1) = u ^ (i + j) * v ^ (i + j) := by
      rw [pow_one]
      calc u ^ i * v ^ j * τ * (u ^ i * v ^ j * τ) =
            u ^ i * v ^ j * (τ * (u ^ i * v ^ j) * τ) := by group
        _ = u ^ i * v ^ j * (v ^ i * u ^ j) := by rw [h1]
        _ = (u ^ i * v ^ j) * (u ^ j * v ^ i) := by rw [← (huv.pow_pow j i).eq]
        _ = u ^ (i + j) * v ^ (j + i) := hmulform _ _ _ _
        _ = u ^ (i + j) * v ^ (i + j) := by rw [add_comm j i]
    rw [h2] at ht
    have hc : ∀ r : R, v₁ * r = r * v₁ := by rw [← ht]; exact hcent (i + j)
    exact hv₁z (huniq v₁ z hc hzc hv₁2 hz2 hv₁1 hz1)

end Abstract

end CFSG.GH74.KGroups.L3Eps
