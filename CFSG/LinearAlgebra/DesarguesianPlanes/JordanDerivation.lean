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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

namespace CFSG.DesarguesianPlanes

variable {F : Type*} [Field F]

theorem derivation_pow (H : F → F) (hmul : ∀ x y, H (x * y) = x * H y + y * H x) (x : F) :
    ∀ n : ℕ, H (x ^ (n + 1)) = ((n : F) + 1) * x ^ n * H x
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, hmul, derivation_pow H hmul x n]
    push_cast
    ring

theorem derivation_eq_zero [Finite F] (H : F → F)
    (hmul : ∀ x y, H (x * y) = x * H y + y * H x) (x : F) : H x = 0 := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hq : 0 < Fintype.card F := Fintype.card_pos
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card F = n + 1 := ⟨Fintype.card F - 1, by omega⟩
  have h := derivation_pow H hmul x n
  have hcast : ((n : F) + 1) = 0 := by
    have := FiniteField.cast_card_eq_zero F
    rw [hn] at this
    exact_mod_cast this
  rw [← hn, FiniteField.pow_card, hcast, zero_mul, zero_mul] at h
  exact h

theorem biadditive_eq_of_sq_equivariant [Finite F] (h2 : (2 : F) ≠ 0) (P : F → F → F)
    (hadd₁ : ∀ c c' d, P (c + c') d = P c d + P c' d)
    (hadd₂ : ∀ c d d', P c (d + d') = P c d + P c d')
    (hsq : ∀ a c d, a ≠ 0 → P (a * c) (a * d) = a ^ 2 * P c d) (c d : F) :
    P c d = P 1 1 * c * d := by
  have hzero₁ : ∀ d, P 0 d = 0 := fun d => by
    have := hadd₁ 0 0 d
    rw [add_zero] at this
    linear_combination -this
  have hzero₂ : ∀ c, P c 0 = 0 := fun c => by
    have := hadd₂ c 0 0
    rw [add_zero] at this
    linear_combination -this
  have hneg₁ : ∀ c d, P (-c) d = -P c d := fun c d => by
    have := hadd₁ c (-c) d
    rw [add_neg_cancel, hzero₁] at this
    linear_combination -this
  have hinv : ∀ x, x ≠ 0 → P x 1 = x ^ 2 * P 1 x⁻¹ := fun x hx => by
    have := hsq x 1 x⁻¹ hx
    rwa [mul_one, mul_inv_cancel₀ hx] at this
  have hsqid : ∀ x, P (x ^ 2) 1 = 2 * x * P x 1 - x ^ 2 * P 1 1 := by
    intro x
    by_cases hx0 : x = 0
    · subst hx0
      simp [hzero₁]
    by_cases hx1 : x + 1 = 0
    · have hx : x = -1 := by linear_combination hx1
      subst hx
      rw [neg_one_sq, hneg₁]
      ring
    have hxx : x ^ 2 + x ≠ 0 := by
      have : x ^ 2 + x = x * (x + 1) := by ring
      rw [this]
      exact mul_ne_zero hx0 hx1
    have hsplit : x⁻¹ = (x + 1)⁻¹ + (x ^ 2 + x)⁻¹ := by
      field_simp
    have h1 := hinv x hx0
    have h2' := hinv (x + 1) hx1
    have h3 := hinv (x ^ 2 + x) hxx
    rw [hsplit, hadd₂] at h1
    have hadd1 : P (x + 1) 1 = P x 1 + P 1 1 := hadd₁ x 1 1
    have hadd2 : P (x ^ 2 + x) 1 = P (x ^ 2) 1 + P x 1 := hadd₁ (x ^ 2) x 1
    have e2 : P 1 (x + 1)⁻¹ = (P x 1 + P 1 1) / (x + 1) ^ 2 := by
      rw [← hadd1, h2']
      field_simp
    have e3 : P 1 (x ^ 2 + x)⁻¹ = (P (x ^ 2) 1 + P x 1) / (x ^ 2 + x) ^ 2 := by
      rw [← hadd2, h3]
      field_simp
    rw [e2, e3] at h1
    have hx2 : x ^ 2 + x = x * (x + 1) := by ring
    rw [hx2] at h1
    field_simp at h1
    linear_combination -h1
  set H : F → F := fun x => P x 1 - x * P 1 1 with hH
  have Hadd : ∀ x y, H (x + y) = H x + H y := fun x y => by
    simp only [hH, hadd₁]
    ring
  have Hsq : ∀ x, H (x ^ 2) = 2 * x * H x := fun x => by
    simp only [hH, hsqid]
    ring
  have Hmul : ∀ x y, H (x * y) = x * H y + y * H x := by
    intro x y
    have h := Hsq (x + y)
    rw [show (x + y) ^ 2 = x ^ 2 + (2 * (x * y) + y ^ 2) by ring, Hadd, Hadd, Hsq, Hsq,
      Hadd x y] at h
    have h2xy : H (2 * (x * y)) = 2 * H (x * y) := by
      rw [two_mul, Hadd, two_mul]
    rw [h2xy] at h
    have : 2 * (H (x * y) - (x * H y + y * H x)) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 h2
    · linear_combination h0
  have hH0 : ∀ x, P x 1 = x * P 1 1 := fun x => by
    have := derivation_eq_zero H Hmul x
    simp only [hH] at this
    linear_combination this
  by_cases hc : c = 0
  · subst hc
    simp [hzero₁]
  have hcd : P c d = c ^ 2 * P 1 (d / c) := by
    have := hsq c 1 (d / c) hc
    rwa [mul_one, mul_div_cancel₀ d hc] at this
  have h1t : ∀ t, P 1 t = t * P 1 1 := by
    intro t
    by_cases ht : t = 0
    · subst ht
      simp [hzero₂]
    have := hsq t t⁻¹ 1 ht
    rw [mul_inv_cancel₀ ht, mul_one, hH0] at this
    rw [this]
    field_simp
  rw [hcd, h1t]
  field_simp

end CFSG.DesarguesianPlanes
