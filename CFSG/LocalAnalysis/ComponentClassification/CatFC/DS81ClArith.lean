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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.ComponentClassification.CatFC.DS81.ClArith

theorem two_pow_mod_of_two_pow_eleven {p : ℕ} (hp : 2 ^ 11 % p = 1) (m : ℕ) :
    2 ^ m % p = 2 ^ (m % 11) % p := by
  conv_lhs => rw [← Nat.div_add_mod m 11, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod, hp, one_pow, Nat.one_mod_eq_one.mpr (by
    rintro rfl; simp at hp), one_mul, Nat.mod_mod]

theorem dvd_two_pow_sub_one_iff_mod {p : ℕ} (m : ℕ) : p ∣ 2 ^ m - 1 ↔ 1 % p = 2 ^ m % p :=
  (Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).symm

theorem twentythree_dvd_two_pow_sub_one_iff (m : ℕ) : 23 ∣ 2 ^ m - 1 ↔ 11 ∣ m := by
  rw [dvd_two_pow_sub_one_iff_mod, two_pow_mod_of_two_pow_eleven (by norm_num) m,
    Nat.dvd_iff_mod_eq_zero]
  have h := Nat.mod_lt m (by norm_num : 0 < 11)
  generalize m % 11 = r at h ⊢
  interval_cases r <;> decide

theorem eightynine_dvd_two_pow_sub_one_iff (m : ℕ) : 89 ∣ 2 ^ m - 1 ↔ 11 ∣ m := by
  rw [dvd_two_pow_sub_one_iff_mod, two_pow_mod_of_two_pow_eleven (by norm_num) m,
    Nat.dvd_iff_mod_eq_zero]
  have h := Nat.mod_lt m (by norm_num : 0 < 11)
  generalize m % 11 = r at h ⊢
  interval_cases r <;> decide

theorem not_twentythree_dvd_two_pow_add_one (m : ℕ) : ¬ 23 ∣ 2 ^ m + 1 := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, two_pow_mod_of_two_pow_eleven (by norm_num) m]
  have h := Nat.mod_lt m (by norm_num : 0 < 11)
  generalize m % 11 = r at h ⊢
  interval_cases r <;> decide

theorem not_eightynine_dvd_two_pow_add_one (m : ℕ) : ¬ 89 ∣ 2 ^ m + 1 := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, two_pow_mod_of_two_pow_eleven (by norm_num) m]
  have h := Nat.mod_lt m (by norm_num : 0 < 11)
  generalize m % 11 = r at h ⊢
  interval_cases r <;> decide

end CFSG.ComponentClassification.CatFC.DS81.ClArith

namespace CFSG.ComponentClassification.CatFC.DS81.ClArith

theorem pow_two_pow_ne_inv {F : Type} [Field F] {ζ : F} {b : ℕ}
    (hζ : ζ ^ (23 ^ b) = 1) (h1 : ζ ≠ 1) (s : ℕ) : ζ ^ (2 ^ s) ≠ ζ⁻¹ := by
  intro h
  have h0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero _ (by norm_num))] at hζ
    exact zero_ne_one hζ
  have hs : ζ ^ (2 ^ s + 1) = 1 := by
    rw [pow_succ, h, inv_mul_cancel₀ h0]
  have hd1 : orderOf ζ ∣ 23 ^ b := orderOf_dvd_of_pow_eq_one hζ
  have hd2 : orderOf ζ ∣ 2 ^ s + 1 := orderOf_dvd_of_pow_eq_one hs
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 23)).mp hd1
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hk'
    exact h1 hk'
  have : 23 ∣ 2 ^ s + 1 := by
    rw [hk'] at hd2
    exact (dvd_pow_self 23 hk0).trans hd2
  exact not_twentythree_dvd_two_pow_add_one s this

theorem eightynine_dvd_card_units {F : Type} [Field F] [Finite F] [CharP F 2] {ζ : Fˣ}
    (h : 23 ∣ orderOf ζ) : 89 ∣ Nat.card Fˣ := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨m, -, hm⟩ := FiniteField.card F 2
  have hu : Nat.card Fˣ = 2 ^ (m : ℕ) - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, hm]
  have h23 : 23 ∣ 2 ^ (m : ℕ) - 1 := hu ▸ h.trans (orderOf_dvd_natCard ζ)
  rw [hu, eightynine_dvd_two_pow_sub_one_iff]
  exact (twentythree_dvd_two_pow_sub_one_iff _).mp h23

end CFSG.ComponentClassification.CatFC.DS81.ClArith
