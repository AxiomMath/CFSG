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

namespace CFSG.RankTwoShapes

theorem two_pow_dvd_sub_one_or_add_one {j : ℕ} {u : ℤ} (hu : u ^ 2 ≡ 1 [ZMOD 2 ^ (j + 3)]) :
    (2 : ℤ) ^ (j + 2) ∣ u - 1 ∨ (2 : ℤ) ^ (j + 2) ∣ u + 1 := by
  have hdvd : (2 : ℤ) ^ (j + 3) ∣ u ^ 2 - 1 := (Int.ModEq.dvd hu.symm)
  have h2 : (2 : ℤ) ^ (j + 2) = 2 * 2 ^ (j + 1) := by ring
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' u
  · exfalso
    have h2dvd : (2 : ℤ) ∣ u ^ 2 - 1 :=
      dvd_trans (dvd_pow_self 2 (by omega : j + 3 ≠ 0)) hdvd
    subst hm
    have hsq : (2 * m) ^ 2 - 1 = 2 * (2 * m ^ 2) - 1 := by ring
    rw [hsq] at h2dvd
    generalize m ^ 2 = M at h2dvd
    omega
  · subst hm
    have hfac : (2 * m + 1) ^ 2 - 1 = 2 ^ 2 * (m * (m + 1)) := by ring
    have hpow : (2 : ℤ) ^ (j + 3) = 2 ^ 2 * 2 ^ (j + 1) := by ring
    rw [hfac, hpow] at hdvd
    have hm' : (2 : ℤ) ^ (j + 1) ∣ m * (m + 1) :=
      (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ^ 2 ≠ 0)).mp hdvd
    obtain ⟨p, hp | hp⟩ := Int.even_or_odd' m
    · left
      have hcop : IsCoprime ((2 : ℤ) ^ (j + 1)) (m + 1) := by
        apply IsCoprime.pow_left
        exact ⟨-p, 1, by rw [hp]; ring⟩
      have hdm : (2 : ℤ) ^ (j + 1) ∣ m := hcop.dvd_of_dvd_mul_right hm'
      rw [h2, show 2 * m + 1 - 1 = 2 * m by ring]
      exact mul_dvd_mul_left 2 hdm
    · right
      have hcop : IsCoprime ((2 : ℤ) ^ (j + 1)) m := by
        apply IsCoprime.pow_left
        exact ⟨-p, 1, by rw [hp]; ring⟩
      have hdm : (2 : ℤ) ^ (j + 1) ∣ m + 1 := hcop.dvd_of_dvd_mul_left hm'
      rw [h2, show 2 * m + 1 + 1 = 2 * (m + 1) by ring]
      exact mul_dvd_mul_left 2 hdm

theorem sq_eq_one_mod_two_pow {k : ℕ} (hk : 3 ≤ k) {u : ℤ} (hu : u ^ 2 ≡ 1 [ZMOD 2 ^ k]) :
    u ≡ 1 [ZMOD 2 ^ k] ∨ u ≡ -1 [ZMOD 2 ^ k] ∨ u ≡ 1 + 2 ^ (k - 1) [ZMOD 2 ^ k] ∨
      u ≡ -1 + 2 ^ (k - 1) [ZMOD 2 ^ k] := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  rw [show j + 3 - 1 = j + 2 by omega]
  have h3 : (2 : ℤ) ^ (j + 3) = 2 * 2 ^ (j + 2) := by ring
  rcases two_pow_dvd_sub_one_or_add_one hu with ⟨s, hs⟩ | ⟨s, hs⟩
  · obtain ⟨q, hq | hq⟩ := Int.even_or_odd' s
    · left
      refine (Int.modEq_iff_dvd.mpr ⟨q, ?_⟩).symm
      rw [h3]
      linear_combination hs + 2 ^ (j + 2) * hq
    · right; right; left
      refine (Int.modEq_iff_dvd.mpr ⟨q, ?_⟩).symm
      rw [h3]
      linear_combination hs + 2 ^ (j + 2) * hq
  · obtain ⟨q, hq | hq⟩ := Int.even_or_odd' s
    · right; left
      refine (Int.modEq_iff_dvd.mpr ⟨q, ?_⟩).symm
      rw [h3]
      linear_combination hs + 2 ^ (j + 2) * hq
    · right; right; right
      refine (Int.modEq_iff_dvd.mpr ⟨q, ?_⟩).symm
      rw [h3]
      linear_combination hs + 2 ^ (j + 2) * hq

theorem sq_eq_one_mod_four {u : ℤ} (hu : u ^ 2 ≡ 1 [ZMOD 4]) :
    u ≡ 1 [ZMOD 4] ∨ u ≡ -1 [ZMOD 4] := by
  have hz : ∀ v : ZMod 4, v ^ 2 = 1 → v = 1 ∨ v = -1 := by decide
  have hcast : ((u : ZMod 4)) ^ 2 = 1 := by
    have h := (ZMod.intCast_eq_intCast_iff (u ^ 2) 1 4).mpr (by exact_mod_cast hu)
    push_cast at h
    exact h
  rcases hz _ hcast with h | h
  · left
    have h' : ((u : ℤ) : ZMod 4) = ((1 : ℤ) : ZMod 4) := by simpa using h
    exact_mod_cast (ZMod.intCast_eq_intCast_iff u 1 4).mp h'
  · right
    have h' : ((u : ℤ) : ZMod 4) = ((-1 : ℤ) : ZMod 4) := by simpa using h
    exact_mod_cast (ZMod.intCast_eq_intCast_iff u (-1) 4).mp h'

theorem zmod_sq_eq_one_two_pow {k : ℕ} (hk : 3 ≤ k) (u : ZMod (2 ^ k)) (hu : u ^ 2 = 1) :
    u = 1 ∨ u = -1 ∨ u = 1 + 2 ^ (k - 1) ∨ u = -1 + 2 ^ (k - 1) := by
  obtain ⟨v, rfl⟩ := ZMod.intCast_surjective u
  have hv : v ^ 2 ≡ 1 [ZMOD 2 ^ k] := by
    have h := (ZMod.intCast_eq_intCast_iff (v ^ 2) 1 (2 ^ k)).mp (by push_cast; exact hu)
    exact_mod_cast h
  have hcast : ∀ w : ℤ, v ≡ w [ZMOD 2 ^ k] → ((v : ℤ) : ZMod (2 ^ k)) = ((w : ℤ) : ZMod (2 ^ k)) :=
    fun w hw => (ZMod.intCast_eq_intCast_iff v w (2 ^ k)).mpr (by exact_mod_cast hw)
  rcases sq_eq_one_mod_two_pow hk hv with h | h | h | h
  · left; simpa using hcast _ h
  · right; left; simpa using hcast _ h
  · right; right; left; simpa using hcast _ h
  · right; right; right; simpa using hcast _ h

theorem zmod_four_sq_eq_one (u : ZMod 4) (hu : u ^ 2 = 1) : u = 1 ∨ u = -1 := by
  revert u
  decide

end CFSG.RankTwoShapes
