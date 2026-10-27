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
public import Mathlib.Data.Int.Star
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

namespace CFSG.ClassicalInvolution.Asc77.A3Mod

variable {G : Type*} [Group G]

section NormalForm

variable {x₁ x₂ x₃ : G} (c12 : Commute x₁ x₂) (c13 : Commute x₁ x₃) (c23 : Commute x₂ x₃)

include c12 c13 c23

theorem exists_normal_form {a : G} (ha : a ∈ Subgroup.closure ({x₁, x₂, x₃} : Set G)) :
    ∃ i j k : ℤ, a = x₁ ^ i * x₂ ^ j * x₃ ^ k := by
  have hc12 : ∀ a b : ℤ, x₁ ^ a * x₂ ^ b = x₂ ^ b * x₁ ^ a := fun a b => (c12.zpow_zpow a b).eq
  have hc13 : ∀ a b : ℤ, x₁ ^ a * x₃ ^ b = x₃ ^ b * x₁ ^ a := fun a b => (c13.zpow_zpow a b).eq
  have hc23 : ∀ a b : ℤ, x₂ ^ a * x₃ ^ b = x₃ ^ b * x₂ ^ a := fun a b => (c23.zpow_zpow a b).eq
  induction ha using Subgroup.closure_induction with
  | mem y hy =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact ⟨1, 0, 0, by simp⟩
    · exact ⟨0, 1, 0, by simp⟩
    · exact ⟨0, 0, 1, by simp⟩
  | one => exact ⟨0, 0, 0, by simp⟩
  | mul y z _ _ hy hz =>
    obtain ⟨i, j, k, rfl⟩ := hy
    obtain ⟨i', j', k', rfl⟩ := hz
    refine ⟨i + i', j + j', k + k', ?_⟩
    calc x₁ ^ i * x₂ ^ j * x₃ ^ k * (x₁ ^ i' * x₂ ^ j' * x₃ ^ k')
        = x₁ ^ i * x₂ ^ j * (x₃ ^ k * x₁ ^ i') * x₂ ^ j' * x₃ ^ k' := by group
      _ = x₁ ^ i * x₂ ^ j * (x₁ ^ i' * x₃ ^ k) * x₂ ^ j' * x₃ ^ k' := by rw [← hc13 i' k]
      _ = x₁ ^ i * (x₂ ^ j * x₁ ^ i') * x₃ ^ k * x₂ ^ j' * x₃ ^ k' := by group
      _ = x₁ ^ i * (x₁ ^ i' * x₂ ^ j) * x₃ ^ k * x₂ ^ j' * x₃ ^ k' := by rw [← hc12 i' j]
      _ = x₁ ^ i * x₁ ^ i' * x₂ ^ j * (x₃ ^ k * x₂ ^ j') * x₃ ^ k' := by group
      _ = x₁ ^ i * x₁ ^ i' * x₂ ^ j * (x₂ ^ j' * x₃ ^ k) * x₃ ^ k' := by rw [← hc23 j' k]
      _ = x₁ ^ (i + i') * x₂ ^ (j + j') * x₃ ^ (k + k') := by
        rw [zpow_add, zpow_add, zpow_add]; group
  | inv y _ hy =>
    obtain ⟨i, j, k, rfl⟩ := hy
    refine ⟨-i, -j, -k, ?_⟩
    have hXY := c12.zpow_zpow (-i) (-j)
    have hXZ := c13.zpow_zpow (-i) (-k)
    have hYZ := c23.zpow_zpow (-j) (-k)
    calc (x₁ ^ i * x₂ ^ j * x₃ ^ k)⁻¹ = x₃ ^ (-k) * x₂ ^ (-j) * x₁ ^ (-i) := by group
      _ = x₃ ^ (-k) * (x₂ ^ (-j) * x₁ ^ (-i)) := by group
      _ = x₃ ^ (-k) * (x₁ ^ (-i) * x₂ ^ (-j)) := by rw [hXY.eq]
      _ = (x₃ ^ (-k) * x₁ ^ (-i)) * x₂ ^ (-j) := by group
      _ = (x₁ ^ (-i) * x₃ ^ (-k)) * x₂ ^ (-j) := by rw [hXZ.eq]
      _ = x₁ ^ (-i) * (x₃ ^ (-k) * x₂ ^ (-j)) := by group
      _ = x₁ ^ (-i) * (x₂ ^ (-j) * x₃ ^ (-k)) := by rw [hYZ.eq]
      _ = x₁ ^ (-i) * x₂ ^ (-j) * x₃ ^ (-k) := by group

end NormalForm

section Conj

variable {x₁ x₂ x₃ r t s : G}

theorem conj_zpow_nf (g : G) (i j k : ℤ) :
    g * (x₁ ^ i * x₂ ^ j * x₃ ^ k) * g⁻¹ =
      (g * x₁ * g⁻¹) ^ i * (g * x₂ * g⁻¹) ^ j * (g * x₃ * g⁻¹) ^ k := by
  rw [conj_zpow, conj_zpow, conj_zpow]
  group

theorem conj_nf_r (c12 : Commute x₁ x₂) (c13 : Commute x₁ x₃) (r₁ : r * x₁ * r⁻¹ = x₁⁻¹)
    (r₂ : r * x₂ * r⁻¹ = x₂) (r₃ : r * x₃ * r⁻¹ = x₃ * x₁) (i j k : ℤ) :
    r * (x₁ ^ i * x₂ ^ j * x₃ ^ k) * r⁻¹ = x₁ ^ (k - i) * x₂ ^ j * x₃ ^ k := by
  rw [conj_zpow_nf, r₁, r₂, r₃, c13.symm.mul_zpow, inv_zpow, ← zpow_neg]
  have h1 := (c13.zpow_zpow k k).eq
  have h2 := (c12.zpow_zpow k j).eq
  calc x₁ ^ (-i) * x₂ ^ j * (x₃ ^ k * x₁ ^ k)
      = x₁ ^ (-i) * x₂ ^ j * (x₁ ^ k * x₃ ^ k) := by rw [← h1]
    _ = x₁ ^ (-i) * (x₂ ^ j * x₁ ^ k) * x₃ ^ k := by group
    _ = x₁ ^ (-i) * (x₁ ^ k * x₂ ^ j) * x₃ ^ k := by rw [← h2]
    _ = x₁ ^ (k - i) * x₂ ^ j * x₃ ^ k := by
      rw [sub_eq_neg_add, zpow_add]; group

theorem conj_nf_t (c23 : Commute x₂ x₃) (t₁ : t * x₁ * t⁻¹ = x₁) (t₂ : t * x₂ * t⁻¹ = x₂⁻¹)
    (t₃ : t * x₃ * t⁻¹ = x₃ * x₂) (i j k : ℤ) :
    t * (x₁ ^ i * x₂ ^ j * x₃ ^ k) * t⁻¹ = x₁ ^ i * x₂ ^ (k - j) * x₃ ^ k := by
  rw [conj_zpow_nf, t₁, t₂, t₃, c23.symm.mul_zpow, inv_zpow, ← zpow_neg]
  have h1 := (c23.zpow_zpow k k).eq
  calc x₁ ^ i * x₂ ^ (-j) * (x₃ ^ k * x₂ ^ k)
      = x₁ ^ i * x₂ ^ (-j) * (x₂ ^ k * x₃ ^ k) := by rw [← h1]
    _ = x₁ ^ i * (x₂ ^ (-j) * x₂ ^ k) * x₃ ^ k := by group
    _ = x₁ ^ i * x₂ ^ (k - j) * x₃ ^ k := by
      rw [sub_eq_neg_add, zpow_add]

theorem conj_nf_s (c13 : Commute x₁ x₃) (c23 : Commute x₂ x₃) (s₁ : s * x₁ * s⁻¹ = x₁ * x₃)
    (s₂ : s * x₂ * s⁻¹ = x₂ * x₃) (s₃ : s * x₃ * s⁻¹ = x₃⁻¹) (i j k : ℤ) :
    s * (x₁ ^ i * x₂ ^ j * x₃ ^ k) * s⁻¹ = x₁ ^ i * x₂ ^ j * x₃ ^ (i + j - k) := by
  rw [conj_zpow_nf, s₁, s₂, s₃, c13.mul_zpow, c23.mul_zpow, inv_zpow, ← zpow_neg]
  calc x₁ ^ i * x₃ ^ i * (x₂ ^ j * x₃ ^ j) * x₃ ^ (-k)
      = x₁ ^ i * (x₃ ^ i * x₂ ^ j) * x₃ ^ j * x₃ ^ (-k) := by group
    _ = x₁ ^ i * (x₂ ^ j * x₃ ^ i) * x₃ ^ j * x₃ ^ (-k) := by
        rw [← (c23.zpow_zpow j i).eq]
    _ = x₁ ^ i * x₂ ^ j * (x₃ ^ i * x₃ ^ j * x₃ ^ (-k)) := by group
    _ = x₁ ^ i * x₂ ^ j * x₃ ^ (i + j - k) := by
      rw [← zpow_add, ← zpow_add, sub_eq_add_neg]

end Conj

section Triple

variable {x₁ x₂ x₃ : G} {m : ℕ}

theorem pow_triple (c12 : Commute x₁ x₂) (c13 : Commute x₁ x₃) (c23 : Commute x₂ x₃) (e : ℤ) :
    (x₁ * x₂⁻¹ * x₃ ^ 2) ^ e = x₁ ^ e * x₂ ^ (-e) * x₃ ^ (2 * e) := by
  have hcomm : Commute (x₁ * x₂⁻¹) (x₃ ^ 2) :=
    (c13.pow_right 2).mul_left (c23.inv_left.pow_right 2)
  rw [hcomm.mul_zpow, c12.inv_right.mul_zpow, inv_zpow, ← zpow_neg, ← zpow_natCast, ← zpow_mul]
  norm_num

theorem triple_facts (c12 : Commute x₁ x₂) (c13 : Commute x₁ x₃) (c23 : Commute x₂ x₃)
    (o₃ : x₃ ^ (4 * m) = 1) (hz : x₁ ^ (2 * m) = x₂ ^ (2 * m)) :
    ((x₁ * x₂⁻¹ * x₃ ^ 2) ^ m) ^ 2 = 1 ∧ (x₁ ^ m * (x₂ ^ m)⁻¹) ^ 2 = 1 ∧
      (x₁ ^ m * (x₂ ^ m)⁻¹) * (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m = x₃ ^ (2 * m) := by
  have hz' : x₁ ^ ((m : ℤ) * 2) = x₂ ^ ((m : ℤ) * 2) := by
    rw [show (m : ℤ) * 2 = ((2 * m : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast]
    exact hz
  have h3 : x₃ ^ (2 * ((m : ℤ) * 2)) = 1 := by
    rw [show (2 : ℤ) * ((m : ℤ) * 2) = ((4 * m : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    exact o₃
  have hX : ∀ e : ℤ, (x₁ * x₂⁻¹ * x₃ ^ 2) ^ e = x₁ ^ e * x₂ ^ (-e) * x₃ ^ (2 * e) :=
    pow_triple c12 c13 c23
  have hm : (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m = x₁ ^ (m : ℤ) * x₂ ^ (-(m : ℤ)) * x₃ ^ (2 * (m : ℤ)) := by
    rw [← zpow_natCast, hX]
  refine ⟨?_, ?_, ?_⟩
  · rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, hX]
    push_cast
    rw [show (m : ℤ) * 2 = (m : ℤ) * 2 from rfl, zpow_neg, hz', mul_inv_cancel, one_mul, h3]
  · have h12 : Commute (x₁ ^ m) (x₂ ^ m)⁻¹ := (c12.pow_pow m m).inv_right
    rw [h12.mul_pow]
    have : (x₁ ^ m) ^ 2 = (x₂ ^ m) ^ 2 := by
      rw [← pow_mul, ← pow_mul, mul_comm m 2]
      exact hz
    rw [inv_pow, this, mul_inv_cancel]
  · rw [hm, ← zpow_natCast x₁ m, ← zpow_natCast x₂ m, ← zpow_neg]
    have hAB : Commute (x₁ ^ (m : ℤ)) (x₂ ^ (-(m : ℤ))) := c12.zpow_zpow _ _
    have h1 : x₁ ^ (m : ℤ) * x₂ ^ (-(m : ℤ)) * (x₁ ^ (m : ℤ) * x₂ ^ (-(m : ℤ)) *
        x₃ ^ (2 * (m : ℤ))) = (x₁ ^ (m : ℤ) * x₁ ^ (m : ℤ)) * (x₂ ^ (-(m : ℤ)) *
        x₂ ^ (-(m : ℤ))) * x₃ ^ (2 * (m : ℤ)) := by
      calc x₁ ^ (m : ℤ) * x₂ ^ (-(m : ℤ)) * (x₁ ^ (m : ℤ) * x₂ ^ (-(m : ℤ)) *
            x₃ ^ (2 * (m : ℤ)))
          = x₁ ^ (m : ℤ) * (x₂ ^ (-(m : ℤ)) * x₁ ^ (m : ℤ)) * x₂ ^ (-(m : ℤ)) *
              x₃ ^ (2 * (m : ℤ)) := by group
        _ = x₁ ^ (m : ℤ) * (x₁ ^ (m : ℤ) * x₂ ^ (-(m : ℤ))) * x₂ ^ (-(m : ℤ)) *
              x₃ ^ (2 * (m : ℤ)) := by rw [← hAB.eq]
        _ = _ := by group
    have e1 : x₁ ^ (m : ℤ) * x₁ ^ (m : ℤ) = x₁ ^ (2 * (m : ℤ)) := by rw [← zpow_add, two_mul]
    have e2 : x₂ ^ (-(m : ℤ)) * x₂ ^ (-(m : ℤ)) = (x₂ ^ (2 * (m : ℤ)))⁻¹ := by
      rw [← zpow_add, ← zpow_neg]
      congr 1
      ring
    have hz'' : x₁ ^ (2 * (m : ℤ)) = x₂ ^ (2 * (m : ℤ)) := by
      rw [show 2 * (m : ℤ) = ((2 * m : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast]
      exact hz
    rw [h1, e1, e2, hz'', mul_inv_cancel, one_mul,
      show 2 * (m : ℤ) = ((2 * m : ℕ) : ℤ) by push_cast; ring, zpow_natCast]

end Triple

section Main

variable {x₁ x₂ x₃ r t s a : G} {m : ℕ}

theorem fixed_eq_one_or (c12 : Commute x₁ x₂) (c13 : Commute x₁ x₃)
    (c23 : Commute x₂ x₃) (o₁ : orderOf x₁ = 4 * m) (o₂ : orderOf x₂ = 4 * m)
    (o₃ : orderOf x₃ = 4 * m) (hz : x₁ ^ (2 * m) = x₂ ^ (2 * m))
    (r₁ : r * x₁ * r⁻¹ = x₁⁻¹) (r₂ : r * x₂ * r⁻¹ = x₂) (r₃ : r * x₃ * r⁻¹ = x₃ * x₁)
    (t₁ : t * x₁ * t⁻¹ = x₁) (t₂ : t * x₂ * t⁻¹ = x₂⁻¹) (t₃ : t * x₃ * t⁻¹ = x₃ * x₂)
    (s₁ : s * x₁ * s⁻¹ = x₁ * x₃) (s₂ : s * x₂ * s⁻¹ = x₂ * x₃) (s₃ : s * x₃ * s⁻¹ = x₃⁻¹)
    (ha : a ∈ Subgroup.closure ({x₁, x₂, x₃} : Set G)) (hra : r * a * r⁻¹ = a)
    (hta : t * a * t⁻¹ = a) (hsa : s * a * s⁻¹ = a) :
    a = 1 ∨ a = (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m := by
  obtain ⟨i, j, k, rfl⟩ := exists_normal_form c12 c13 c23 ha
  have key : ∀ (x : G) (n : ℕ) (e : ℤ), orderOf x = n → x ^ e = 1 → (n : ℤ) ∣ e := by
    intro x n e hx he
    rw [← hx]
    exact orderOf_dvd_iff_zpow_eq_one.mpr he
  have A : ((4 * m : ℕ) : ℤ) ∣ k - 2 * i := by
    have h := conj_nf_r c12 c13 r₁ r₂ r₃ i j k
    rw [hra] at h
    have h1 : x₁ ^ i = x₁ ^ (k - i) := mul_right_cancel (mul_right_cancel h)
    refine key x₁ _ _ o₁ ?_
    rw [show k - 2 * i = (k - i) - i by ring, zpow_sub, ← h1, mul_inv_cancel]
  have B : ((4 * m : ℕ) : ℤ) ∣ k - 2 * j := by
    have h := conj_nf_t c23 t₁ t₂ t₃ i j k
    rw [hta] at h
    have h1 : x₂ ^ j = x₂ ^ (k - j) := by
      have h2 := mul_right_cancel h
      exact mul_left_cancel h2
    refine key x₂ _ _ o₂ ?_
    rw [show k - 2 * j = (k - j) - j by ring, zpow_sub, ← h1, mul_inv_cancel]
  have C : ((4 * m : ℕ) : ℤ) ∣ i + j - 2 * k := by
    have h := conj_nf_s c13 c23 s₁ s₂ s₃ i j k
    rw [hsa] at h
    have h1 : x₃ ^ k = x₃ ^ (i + j - k) := mul_left_cancel h
    refine key x₃ _ _ o₃ ?_
    rw [show i + j - 2 * k = (i + j - k) - k by ring, zpow_sub, ← h1, mul_inv_cancel]
  have hpow : ∀ (x : G) (n : ℕ) (e : ℤ), orderOf x = n → x ^ ((n : ℤ) * e) = 1 := by
    intro x n e hx
    rw [zpow_mul, zpow_natCast, ← hx, pow_orderOf_eq_one, one_zpow]
  have h4i : ((4 * m : ℕ) : ℤ) ∣ 4 * i := by
    have : 4 * i = -3 * (k - 2 * i) - (k - 2 * j) - 2 * (i + j - 2 * k) := by ring
    rw [this]
    exact dvd_sub (dvd_sub (A.mul_left (-3)) B) (C.mul_left 2)
  have hmi : (m : ℤ) ∣ i := by
    have : (4 : ℤ) * m ∣ 4 * i := by simpa using h4i
    exact (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp this
  have hj3 : ((4 * m : ℕ) : ℤ) ∣ j - 3 * i := by
    have : j - 3 * i = 2 * (k - 2 * i) + (i + j - 2 * k) := by ring
    rw [this]
    exact dvd_add (A.mul_left 2) C
  obtain ⟨κ, hκ⟩ := hmi
  obtain ⟨p, hp⟩ := A
  obtain ⟨q, hq⟩ := hj3
  have hk : k = 2 * ((m : ℤ) * κ) + ((4 * m : ℕ) : ℤ) * p := by rw [← hκ]; linarith
  have hj : j = 3 * ((m : ℤ) * κ) + ((4 * m : ℕ) : ℤ) * q := by rw [← hκ]; linarith
  have e₁ : x₁ ^ i = x₁ ^ ((m : ℤ) * κ) := by rw [hκ]
  have e₂ : x₂ ^ j = x₂ ^ (-((m : ℤ) * κ)) := by
    have h4 : x₂ ^ (4 * ((m : ℤ) * κ)) = 1 := by
      have := hpow x₂ (4 * m) (κ) o₂
      rw [show (4 : ℤ) * ((m : ℤ) * κ) = ((4 * m : ℕ) : ℤ) * κ by push_cast; ring]
      exact this
    rw [hj, zpow_add, hpow x₂ (4 * m) q o₂, mul_one,
      show 3 * ((m : ℤ) * κ) = -((m : ℤ) * κ) + 4 * ((m : ℤ) * κ) by ring, zpow_add, h4, mul_one]
  have e₃ : x₃ ^ k = x₃ ^ (2 * ((m : ℤ) * κ)) := by
    rw [hk, zpow_add, hpow x₃ (4 * m) p o₃, mul_one]
  have hcomm : Commute (x₁ * x₂⁻¹) (x₃ ^ 2) :=
    (c13.pow_right 2).mul_left (c23.inv_left.pow_right 2)
  have hy : ∀ e : ℤ, (x₁ * x₂⁻¹ * x₃ ^ 2) ^ e = x₁ ^ e * x₂ ^ (-e) * x₃ ^ (2 * e) := by
    intro e
    rw [hcomm.mul_zpow, c12.inv_right.mul_zpow, inv_zpow, ← zpow_neg, ← zpow_natCast, ← zpow_mul]
    norm_num
  have hae : x₁ ^ i * x₂ ^ j * x₃ ^ k = ((x₁ * x₂⁻¹ * x₃ ^ 2) ^ m) ^ κ := by
    rw [← zpow_natCast, ← zpow_mul, hy, e₁, e₂, e₃]
  have hsq : ((x₁ * x₂⁻¹ * x₃ ^ 2) ^ m) ^ (2 : ℤ) = 1 := by
    rw [← zpow_natCast, ← zpow_mul, hy]
    have hz' : x₁ ^ ((m : ℤ) * 2) = x₂ ^ ((m : ℤ) * 2) := by
      rw [show (m : ℤ) * 2 = ((2 * m : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast]
      exact hz
    have h3 : x₃ ^ (2 * ((m : ℤ) * 2)) = 1 := by
      have := hpow x₃ (4 * m) 1 o₃
      rw [show (2 : ℤ) * ((m : ℤ) * 2) = ((4 * m : ℕ) : ℤ) * 1 by push_cast; ring]
      exact this
    rw [zpow_neg, hz', mul_inv_cancel, one_mul, h3]
  rw [hae]
  have hpar : ((x₁ * x₂⁻¹ * x₃ ^ 2) ^ m) ^ κ =
      ((x₁ * x₂⁻¹ * x₃ ^ 2) ^ m) ^ (κ % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv κ 2, zpow_add, zpow_mul, hsq, one_zpow, mul_one]
  rw [hpar]
  rcases Int.emod_two_eq_zero_or_one κ with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

end Main


end CFSG.ClassicalInvolution.Asc77.A3Mod
