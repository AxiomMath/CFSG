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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.QuasithinUnique.Lin2.OddRank

theorem exists_prime_dvd_of_two_le {g : ℕ} (hg : 2 ≤ g) :
    ∃ p : ℕ, p.Prime ∧ p ∣ 2 ^ g - 1 := by
  refine Nat.exists_prime_and_dvd ?_
  have : 2 ^ 2 ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  omega

theorem pow_sub_one_dvd {g a : ℕ} (h : g ∣ a) : 2 ^ g - 1 ∣ 2 ^ a - 1 := by
  obtain ⟨k, rfl⟩ := h
  rw [pow_mul]
  exact Nat.sub_one_dvd_pow_sub_one _ _

theorem ne_two_of_dvd_two_pow_sub_one {g p : ℕ} (hg : 1 ≤ g) (h : p ∣ 2 ^ g - 1) : p ≠ 2 := by
  rintro rfl
  have h2 : 2 ∣ 2 ^ g := dvd_pow_self 2 (by omega)
  have h3 : 0 < 2 ^ g := Nat.two_pow_pos g
  omega

theorem exists_prime_ne_three_dvd {n : ℕ} (hn : 2 ≤ n) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 3 ∧ ℓ ∣ 2 ^ (2 * n) - 1 := by
  have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hfac : 2 ^ (2 * n) - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
    have h := Nat.sq_sub_sq (2 ^ n) 1
    rw [one_pow, ← pow_mul, mul_comm n 2] at h
    rw [h, mul_comm]
  by_contra hcon
  push Not at hcon
  obtain ⟨pa, hpa, hpaa⟩ := Nat.exists_prime_and_dvd (n := 2 ^ n - 1) (by omega)
  obtain ⟨pb, hpb, hpbb⟩ := Nat.exists_prime_and_dvd (n := 2 ^ n + 1) (by omega)
  have ha3 : pa = 3 := by
    by_contra hne
    exact hcon pa hpa hne (hfac ▸ dvd_mul_of_dvd_left hpaa _)
  have hb3 : pb = 3 := by
    by_contra hne
    exact hcon pb hpb hne (hfac ▸ dvd_mul_of_dvd_right hpbb _)
  subst ha3 hb3
  omega

theorem two_le_gcd_sq {a b ℓ : ℕ} (ha : 0 < a) (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3)
    (h1 : ℓ ∣ 2 ^ (2 * a) - 1) (h2 : ℓ ∣ 2 ^ (2 * b) - 1) : 2 ≤ Nat.gcd a b := by
  have hg : ℓ ∣ 2 ^ Nat.gcd (2 * a) (2 * b) - 1 := by
    rw [← Nat.pow_sub_one_gcd_pow_sub_one]
    exact Nat.dvd_gcd h1 h2
  rw [Nat.gcd_mul_left] at hg
  by_contra hlt
  have hpos : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left _ ha
  have h1' : Nat.gcd a b = 1 := by omega
  rw [h1'] at hg
  norm_num at hg
  exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp hg)

end CFSG.QuasithinUnique.Lin2.OddRank
