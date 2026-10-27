module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

section Abstract

variable {K : Type*} [Group K] (σ : MulAut K)

theorem σ_mem_center {z : K} (hz : z ∈ Subgroup.center K) : σ z ∈ Subgroup.center K := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro k
  have := hz (σ.symm k)
  have h2 := congrArg σ this
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
  exact h2

theorem σ_zpow {k c : K} (hc : c ∈ Subgroup.center K) (h : σ k = c * k) (j : ℤ) :
    σ (k ^ j) = c ^ j * k ^ j := by
  have hcom : Commute c k := (Subgroup.mem_center_iff.mp hc k).symm
  rw [map_zpow, h]
  exact hcom.mul_zpow j

theorem three_part {k c : K} (hc : c ∈ Subgroup.center K) (h : σ k = c * k) {n : ℕ}
    (hk : k ^ 3 ^ n = 1)
    (hZ3 : ∀ z ∈ Subgroup.center K, (∃ m : ℕ, z ^ 3 ^ m = 1) → z ^ 3 = 1) : c ^ 3 = 1 := by
  apply hZ3 c hc ⟨n, ?_⟩
  have h1 := σ_zpow σ hc h ((3 ^ n : ℕ) : ℤ)
  rw [zpow_natCast, zpow_natCast, hk, map_one, mul_one] at h1
  exact h1.symm

theorem triple_central {a b d ℓ : K} (hb : b ∈ Subgroup.center K) (hd : d ∈ Subgroup.center K) :
    (a * ℓ) * (b * ℓ) * (d * ℓ) = (a * b * d) * ℓ ^ 3 := by
  have kb : ℓ * b = b * ℓ := Subgroup.mem_center_iff.mp hb ℓ
  have kd : ℓ * ℓ * d = d * (ℓ * ℓ) := Subgroup.mem_center_iff.mp hd (ℓ * ℓ)
  calc (a * ℓ) * (b * ℓ) * (d * ℓ) = a * (ℓ * b) * ℓ * (d * ℓ) := by simp only [mul_assoc]
    _ = a * (b * ℓ) * ℓ * (d * ℓ) := by rw [kb]
    _ = (a * b) * (ℓ * ℓ * d) * ℓ := by simp only [mul_assoc]
    _ = (a * b) * (d * (ℓ * ℓ)) * ℓ := by rw [kd]
    _ = (a * b * d) * ℓ ^ 3 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem coprime_part (hσ3 : σ ^ 3 = 1) {ℓ c : K} (hc : c ∈ Subgroup.center K) (h : σ ℓ = c * ℓ)
    {t : ℕ} (ht : ℓ ^ t = 1) (h3 : Nat.Coprime 3 t) :
    ∃ k : K, σ k = k ∧ k * ℓ⁻¹ ∈ Subgroup.center K := by
  by_cases ht1 : t = 1
  · subst ht1
    rw [pow_one] at ht
    subst ht
    exact ⟨1, map_one σ, by simp⟩
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at h3
  have ht1' : 1 < t := by omega
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime h3 ht1'
  have hcc : σ c ∈ Subgroup.center K := σ_mem_center σ hc
  have hcc' : σ c * c ∈ Subgroup.center K := Subgroup.mul_mem _ hcc hc
  have s2 : σ (σ ℓ) = σ c * c * ℓ := by rw [h, map_mul, h, mul_assoc]
  have s3 : σ (σ (σ ℓ)) = ℓ := by
    have := congrArg (fun f : MulAut K => f ℓ) hσ3
    simpa [pow_succ, MulAut.mul_apply] using this
  set z₁ : K := c * (σ c * c) with hz₁
  have hz₁c : z₁ ∈ Subgroup.center K := Subgroup.mul_mem _ hc hcc'
  have hg : ℓ * σ ℓ * σ (σ ℓ) = z₁ * ℓ ^ 3 := by
    have := triple_central (a := 1) (ℓ := ℓ) hc hcc'
    rw [s2, h]
    simpa [hz₁] using this
  have hg' : σ (ℓ * σ ℓ * σ (σ ℓ)) = z₁ * ℓ ^ 3 := by
    rw [map_mul, map_mul, s3, s2, h]
    have := triple_central (a := c) (b := σ c * c) (d := 1) (ℓ := ℓ) hcc' (Subgroup.one_mem _)
    simpa [hz₁] using this
  set g := ℓ * σ ℓ * σ (σ ℓ) with hgdef
  have hσg : σ g = g := by rw [hg', hg]
  refine ⟨g ^ m, by rw [map_pow, hσg], ?_⟩
  have hpow : ℓ ^ (3 * m) = ℓ := by
    have h1 : 3 * m = t * (3 * m / t) + 1 := by
      have := Nat.div_add_mod (3 * m) t
      omega
    rw [h1, pow_add, pow_mul, ht, one_pow, one_mul, pow_one]
  have hgm : g ^ m = z₁ ^ m * ℓ := by
    have hcom : Commute z₁ (ℓ ^ 3) := (Subgroup.mem_center_iff.mp hz₁c (ℓ ^ 3)).symm
    rw [hg, hcom.mul_pow, ← pow_mul, hpow]
  rw [hgm, mul_assoc, mul_inv_cancel, mul_one]
  exact Subgroup.pow_mem _ hz₁c m

variable [Finite K]

theorem exists_sigma_normalizing_lift (hσ3 : σ ^ 3 = 1)
    (hZ3 : ∀ z ∈ Subgroup.center K, (∃ m : ℕ, z ^ 3 ^ m = 1) → z ^ 3 = 1)
    {ℓ c : K} (hc : c ∈ Subgroup.center K) (h : σ ℓ = c * ℓ) :
    ∃ k : K, k * ℓ⁻¹ ∈ Subgroup.center K ∧
      ∃ w ∈ Subgroup.center K, w ^ 3 = 1 ∧ σ k = w * k := by
  obtain ⟨e, n', hn', hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos ℓ).ne' 3
    (by norm_num)
  have hcop : Nat.Coprime 3 n' := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hn'
  by_cases hn1 : n' = 1
  · subst hn1
    refine ⟨ℓ, by simp, c, hc, ?_, h⟩
    refine three_part σ hc h (n := e) ?_ hZ3
    rw [← mul_one (3 ^ e), ← hN]
    exact pow_orderOf_eq_one ℓ
  have hn0 : n' ≠ 0 := by
    rintro rfl
    simp at hcop
  have hn1' : 1 < n' := by omega
  have hcop' : Nat.Coprime (3 ^ e) n' := Nat.Coprime.pow_left _ hcop
  obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop' hn1'
  set j₁ : ℤ := ((3 ^ e * s : ℕ) : ℤ) with hj₁
  set j₃ : ℤ := 1 - j₁ with hj₃
  set ℓ₁ : K := ℓ ^ j₁ with hℓ₁
  set ℓ₃ : K := ℓ ^ j₃ with hℓ₃
  have hprod : ℓ₃ * ℓ₁ = ℓ := by
    rw [hℓ₃, hℓ₁, ← zpow_add, hj₃, sub_add_cancel, zpow_one]
  have hcomm : Commute ℓ₃ ℓ₁ := (Commute.refl ℓ).zpow_zpow _ _
  have hσ₁ : σ ℓ₁ = c ^ j₁ * ℓ₁ := σ_zpow σ hc h j₁
  have hσ₃ : σ ℓ₃ = c ^ j₃ * ℓ₃ := σ_zpow σ hc h j₃
  have hℓ₁n : ℓ₁ ^ n' = 1 := by
    rw [hℓ₁, hj₁, zpow_natCast, ← pow_mul, show 3 ^ e * s * n' = orderOf ℓ * s by
      rw [hN]; ring, pow_mul, pow_orderOf_eq_one, one_pow]
  have hℓ₃n : ℓ₃ ^ 3 ^ e = 1 := by
    have hq : 3 ^ e * s = n' * (3 ^ e * s / n') + 1 := by
      have := Nat.div_add_mod (3 ^ e * s) n'
      omega
    have h1 : j₃ * ((3 ^ e : ℕ) : ℤ) = -((orderOf ℓ : ℕ) : ℤ) * ((3 ^ e * s / n' : ℕ) : ℤ) := by
      rw [hj₃, hj₁]
      have hq' : ((3 ^ e * s : ℕ) : ℤ) = (n' : ℤ) * ((3 ^ e * s / n' : ℕ) : ℤ) + 1 := by
        exact_mod_cast hq
      rw [hq', hN]
      push_cast
      ring
    rw [hℓ₃, ← zpow_natCast, ← zpow_mul, h1, zpow_mul, zpow_neg, zpow_natCast,
      zpow_natCast, pow_orderOf_eq_one, inv_one, one_pow]
  obtain ⟨k₁, hk₁σ, hk₁Z⟩ := coprime_part σ hσ3 (Subgroup.zpow_mem _ hc j₁) hσ₁ hℓ₁n hcop
  have hw3 := three_part σ (Subgroup.zpow_mem _ hc j₃) hσ₃ hℓ₃n hZ3
  refine ⟨ℓ₃ * k₁, ?_, c ^ j₃, Subgroup.zpow_mem _ hc j₃, hw3, ?_⟩
  · have h1 : ℓ₃ * k₁ * ℓ⁻¹ = ℓ₃ * (k₁ * ℓ₁⁻¹) * ℓ₃⁻¹ := by rw [← hprod]; group
    rw [h1, Subgroup.mem_center_iff.mp hk₁Z ℓ₃, mul_inv_cancel_right]
    exact hk₁Z
  · rw [map_mul, hσ₃, hk₁σ, mul_assoc]

end Abstract

end CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner
