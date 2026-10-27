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
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Semidihedral.AllPrime

private theorem exists_odd_prime_dvd {n : ℕ} (hn : n % 2 = 1) (hn1 : n ≠ 1) :
    ∃ s : ℕ, s.Prime ∧ s ≠ 2 ∧ s ∣ n := by
  obtain ⟨s, hs, hsn⟩ := Nat.exists_prime_and_dvd hn1
  refine ⟨s, hs, ?_, hsn⟩
  rintro rfl
  omega

private theorem three_pow_mod_twenty (f : ℕ) :
    3 ^ f % 20 = 1 ∨ 3 ^ f % 20 = 3 ∨ 3 ^ f % 20 = 9 ∨ 3 ^ f % 20 = 7 := by
  induction f with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    omega

theorem iv9Reflection_prime_cases {p f r : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hq : 5 < p ^ f) (hr : r.Prime) (hr2 : r ≠ 2) :
    (∃ s : ℕ, s.Prime ∧ s ≠ 2 ∧ s ≠ r ∧ s ∣ p ^ f - 1) ∨
    (∃ s : ℕ, s.Prime ∧ s ≠ 2 ∧ s ≠ r ∧ s ∣ p ^ f + 1) ∨
    (p ^ f % 4 = 3 ∧ p ≠ r) ∨ ((r = 3 ∨ r = 5) ∧ 8 ∣ p ^ f - 1) := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hodd : p ^ f % 2 = 1 := Nat.odd_iff.mp (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hpq : ¬ p ∣ p ^ f - 1 := by
    intro h
    have h1 := Nat.dvd_sub (dvd_pow_self p hf) h
    rw [Nat.sub_sub_self (by omega)] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have h3q : 3 ∣ p ^ f →
      p ^ f % 20 = 1 ∨ p ^ f % 20 = 3 ∨ p ^ f % 20 = 9 ∨ p ^ f % 20 = 7 := by
    intro h
    obtain rfl : p = 3 :=
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.prime_three.dvd_of_dvd_pow h)).symm
    exact three_pow_mod_twenty f
  generalize p ^ f = q at hq hodd hpq h3q ⊢
  by_cases A : ∃ s : ℕ, s.Prime ∧ s ≠ 2 ∧ s ≠ r ∧ s ∣ q - 1
  · exact Or.inl A
  by_cases B : ∃ s : ℕ, s.Prime ∧ s ≠ 2 ∧ s ≠ r ∧ s ∣ q + 1
  · exact Or.inr (Or.inl B)
  have hA : ∀ s : ℕ, s.Prime → s ≠ 2 → s ∣ q - 1 → s = r := fun s hs hs2 hd =>
    by_contra fun h => A ⟨s, hs, hs2, h, hd⟩
  have hB : ∀ s : ℕ, s.Prime → s ≠ 2 → s ∣ q + 1 → s = r := fun s hs hs2 hd =>
    by_contra fun h => B ⟨s, hs, hs2, h, hd⟩
  refine Or.inr (Or.inr ?_)
  by_cases hq3 : q % 4 = 3
  · refine Or.inl ⟨hq3, ?_⟩
    rintro rfl
    obtain ⟨s, hs, hs2, hsd⟩ := exists_odd_prime_dvd (n := (q - 1) / 2) (by omega) (by omega)
    have hsq : s ∣ q - 1 := dvd_trans hsd ⟨2, by omega⟩
    exact hpq (hA s hs hs2 hsq ▸ hsq)
  refine Or.inr ?_
  obtain ⟨s, hs, hs2, hsd⟩ := exists_odd_prime_dvd (n := (q + 1) / 2) (by omega) (by omega)
  have hsq : s ∣ q + 1 := dvd_trans hsd ⟨2, by omega⟩
  have hrq : r ∣ q + 1 := hB s hs hs2 hsq ▸ hsq
  have hC : ∀ t : ℕ, t.Prime → t ≠ 2 → ¬ t ∣ q - 1 := by
    intro t ht ht2 htd
    have hrd : r ∣ q - 1 := hA t ht ht2 htd ▸ htd
    have h2 := Nat.dvd_sub hrq hrd
    rw [show q + 1 - (q - 1) = 2 by omega] at h2
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2)
  have h8 : 8 ∣ q - 1 := by
    by_contra h8
    obtain ⟨t, ht, ht2, htd⟩ := exists_odd_prime_dvd (n := (q - 1) / 4) (by omega) (by omega)
    exact hC t ht ht2 (dvd_trans htd ⟨4, by omega⟩)
  refine ⟨?_, h8⟩
  by_cases h3 : 3 ∣ q
  ·
    right
    rcases h3q h3 with h | h | h | h
    · exact (hC 5 Nat.prime_five (by norm_num) ⟨(q - 1) / 5, by omega⟩).elim
    · omega
    · exact (hB 5 Nat.prime_five (by norm_num) ⟨(q + 1) / 5, by omega⟩).symm
    · omega
  ·
    left
    have h3' : ¬ 3 ∣ q - 1 := hC 3 Nat.prime_three (by norm_num)
    have h31 : 3 ∣ q + 1 := by
      clear * - h3 h3' hq
      omega
    exact (hB 3 Nat.prime_three (by norm_num) h31).symm

end CFSG.Semidihedral.AllPrime
