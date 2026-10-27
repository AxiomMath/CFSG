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
public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.Wreathed.OriginalAllPrime.IVFacts

open Finset

@[expose] def geomPhi (x ε : ℤ) (r : ℕ) : ℤ := ∑ i ∈ range r, x ^ i * ε ^ (r - 1 - i)

theorem geomPhi_mul (x ε : ℤ) (r : ℕ) : geomPhi x ε r * (x - ε) = x ^ r - ε ^ r :=
  geom_sum₂_mul x ε r

theorem eps_pow_of_odd {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {r : ℕ} (hr : Odd r) : ε ^ r = ε := by
  rcases hε with rfl | rfl
  · rw [one_pow]
  · exact hr.neg_one_pow

theorem eps_pow_of_even {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {r : ℕ} (hr : Even r) : ε ^ r = 1 := by
  rcases hε with rfl | rfl
  · rw [one_pow]
  · exact hr.neg_one_pow

theorem eq_geomPhi_mul {x ε A B m : ℤ} {r : ℕ} (hε : ε = 1 ∨ ε = -1) (hr : Odd r) (hm : m ≠ 0)
    (hA : A * m = x ^ r - ε) (hB : B * m = x - ε) : A = geomPhi x ε r * B := by
  apply mul_right_cancel₀ hm
  rw [hA, mul_assoc, hB, geomPhi_mul, eps_pow_of_odd hε hr]

theorem pow_succ_dvd_of_dvd {x ε A B m : ℤ} {r : ℕ} (hε : ε = 1 ∨ ε = -1) (hr : Odd r)
    (hm : m ≠ 0) (hA : A * m = x ^ r - ε) (hB : B * m = x - ε) (hrB : (r : ℤ) ∣ B) {v : ℕ}
    (hv : (r : ℤ) ^ v ∣ B) : (r : ℤ) ^ (v + 1) ∣ A := by
  rw [eq_geomPhi_mul hε hr hm hA hB, pow_succ, mul_comm (geomPhi x ε r)]
  have hrx : (r : ℤ) ∣ x - ε := by
    rw [← hB]
    exact hrB.mul_right m
  exact mul_dvd_mul hv (dvd_geom_sum₂_self hrx)

theorem two_mul_le_pow {x : ℤ} (hx : 3 ≤ x) {r : ℕ} (hr : 3 ≤ r) : 2 * r * x ≤ x ^ r := by
  induction r, hr using Nat.le_induction with
  | base =>
    have h : (6 : ℤ) ≤ x ^ 2 := by nlinarith
    calc 2 * ((3 : ℕ) : ℤ) * x = 6 * x := by norm_num
      _ ≤ x ^ 2 * x := by nlinarith
      _ = x ^ 3 := by ring
  | succ r hr ih =>
    have hx0 : (0 : ℤ) ≤ x := by omega
    have hr3 : (3 : ℤ) ≤ r := by exact_mod_cast hr
    have hrx : (0 : ℤ) ≤ 2 * r * x := by positivity
    calc 2 * ((r + 1 : ℕ) : ℤ) * x = 2 * r * x + 2 * x := by push_cast; ring
      _ ≤ 2 * r * x * x := by nlinarith [mul_nonneg hrx (by omega : (0 : ℤ) ≤ x - 3)]
      _ ≤ x ^ r * x := by nlinarith
      _ = x ^ (r + 1) := by ring

theorem lt_geomPhi {x ε : ℤ} (hx : 3 ≤ x) (hε : ε = 1 ∨ ε = -1) {r : ℕ} (hr : 3 ≤ r)
    (hrodd : Odd r) : (r : ℤ) < geomPhi x ε r := by
  have h1 := geomPhi_mul x ε r
  rw [eps_pow_of_odd hε hrodd] at h1
  have h2 := two_mul_le_pow hx hr
  have hr3 : (3 : ℤ) ≤ r := by exact_mod_cast hr
  have hpos : 0 < x - ε := by rcases hε with rfl | rfl <;> omega
  have h3 : (r : ℤ) * (x - ε) < geomPhi x ε r * (x - ε) := by
    rw [h1]
    rcases hε with rfl | rfl <;> nlinarith
  exact lt_of_mul_lt_mul_right h3 hpos.le

theorem geomPhi_cast_of_eq {s : ℕ} {x ε : ℤ} (h : (x : ZMod s) = (ε : ZMod s)) (r : ℕ) :
    (geomPhi x ε r : ZMod s) = r * (ε : ZMod s) ^ (r - 1) := by
  rw [geomPhi]
  push_cast
  rw [h]
  have key : ∀ i ∈ range r, (ε : ZMod s) ^ i * (ε : ZMod s) ^ (r - 1 - i) =
      (ε : ZMod s) ^ (r - 1) := by
    intro i hi
    rw [← pow_add]
    congr 1
    rw [mem_range] at hi
    omega
  rw [sum_congr rfl key, sum_const, card_range, nsmul_eq_mul]

theorem eq_of_dvd_geomPhi {x ε : ℤ} (hε : ε = 1 ∨ ε = -1) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) {s : ℕ} (hs : s.Prime) (hsΦ : (s : ℤ) ∣ geomPhi x ε r)
    (hsx : (s : ℤ) ∣ x - ε) : s = r := by
  have hxε : (x : ZMod s) = (ε : ZMod s) := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (x - ε) s).mpr hsx
    push_cast at h
    exact sub_eq_zero.mp h
  have hΦ := geomPhi_cast_of_eq hxε r
  rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ s).mpr hsΦ] at hΦ
  have heven : Even (r - 1) := by
    have := hr.eq_two_or_odd'.resolve_left hr2
    obtain ⟨k, hk⟩ := this
    exact ⟨k, by omega⟩
  have hε1 : (ε : ZMod s) ^ (r - 1) = 1 := by
    rw [← Int.cast_pow, eps_pow_of_even hε heven, Int.cast_one]
  rw [hε1, mul_one] at hΦ
  have hsr : s ∣ r := (ZMod.natCast_eq_zero_iff r s).mp hΦ.symm
  exact (Nat.prime_dvd_prime_iff_eq hs hr).mp hsr

theorem not_sq_dvd_geomPhi {x ε : ℤ} (hx : 3 ≤ x) (hε : ε = 1 ∨ ε = -1) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) : ¬ (r : ℤ) ^ 2 ∣ geomPhi x ε r := by
  have hrodd : Odd r := hr.eq_two_or_odd'.resolve_left hr2
  have : Fact r.Prime := ⟨hr⟩
  have hr3 : 3 ≤ r := by
    have := hr.two_le
    obtain ⟨k, hk⟩ := hrodd
    omega
  have hrε : ¬ (r : ℤ) ∣ ε := by
    intro h
    have h1 : (r : ℤ) ∣ 1 := by
      rcases hε with rfl | rfl
      · exact h
      · exact dvd_neg.mp h
    have := Int.eq_one_of_dvd_one (by positivity) h1
    omega
  have h1 := geomPhi_mul x ε r
  rw [eps_pow_of_odd hε hrodd] at h1
  by_cases hrx : (r : ℤ) ∣ x - ε
  ·
    have hrx' : ¬ (r : ℤ) ∣ x := by
      intro h
      apply hrε
      have := dvd_sub h hrx
      rwa [sub_sub_cancel] at this
    have hlte := Int.emultiplicity_pow_sub_pow hr hrodd hrx hrx' r
    rw [eps_pow_of_odd hε hrodd, ← h1, emultiplicity_mul (Nat.prime_iff_prime_int.mp hr),
      Nat.Prime.emultiplicity_self hr] at hlte
    have hne : x - ε ≠ 0 := by rcases hε with rfl | rfl <;> omega
    have hfin : emultiplicity (r : ℤ) (x - ε) ≠ ⊤ := by
      rw [ne_eq, emultiplicity_eq_top, not_not]
      exact Int.finiteMultiplicity_iff.mpr ⟨by
        have := hr.one_lt
        omega, hne⟩
    rw [add_comm (emultiplicity _ (geomPhi x ε r))] at hlte
    have hΦ1 : emultiplicity (r : ℤ) (geomPhi x ε r) = 1 :=
      (WithTop.add_left_cancel hfin hlte)
    intro h2
    have := pow_dvd_iff_le_emultiplicity.mp h2
    rw [hΦ1] at this
    exact absurd this (by norm_num)
  ·
    intro h2
    have hrΦ : (r : ℤ) ∣ geomPhi x ε r := (dvd_pow_self _ (by norm_num)).trans h2
    apply hrx
    have hcast := congrArg (fun z : ℤ => (z : ZMod r)) h1
    simp only [Int.cast_mul, Int.cast_sub, Int.cast_pow] at hcast
    rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mpr hrΦ, zero_mul, ZMod.pow_card] at hcast
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact hcast.symm

theorem exists_prime_dvd_not_dvd {x ε A B m : ℤ} (hx : 3 ≤ x) (hε : ε = 1 ∨ ε = -1)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hm : m ≠ 0) (hA : A * m = x ^ r - ε)
    (hB : B * m = x - ε) : ∃ s : ℕ, s.Prime ∧ s ≠ r ∧ (s : ℤ) ∣ A ∧ ¬ (s : ℤ) ∣ B := by
  have hrodd : Odd r := hr.eq_two_or_odd'.resolve_left hr2
  have hr3 : 3 ≤ r := by
    have := hr.two_le
    obtain ⟨k, hk⟩ := hrodd
    omega
  have hlt := lt_geomPhi hx hε hr3 hrodd
  have hsq := not_sq_dvd_geomPhi hx hε hr hr2
  set Φ := geomPhi x ε r with hΦ
  have hΦpos : 0 < Φ := by have : (0 : ℤ) < r := by positivity
                           omega
  have hex : ∃ s : ℕ, s.Prime ∧ s ≠ r ∧ s ∣ Φ.natAbs := by
    by_contra hne
    push Not at hne
    have hΦ0 : Φ.natAbs ≠ 0 := by omega
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hΦ0
      (fun {d} hd hdvd => by
        by_contra hdr
        exact hne d hd hdr hdvd)
    set k := Φ.natAbs.primeFactorsList.length with hk
    have hk1 : k ≤ 1 := by
      by_contra hk2
      apply hsq
      have : (r : ℤ) ^ 2 ∣ (Φ.natAbs : ℤ) := by
        rw [hpow]
        exact_mod_cast pow_dvd_pow r (by omega)
      rwa [Int.natCast_natAbs, abs_of_pos hΦpos] at this
    have hle : Φ.natAbs ≤ r := by
      rw [hpow]
      calc r ^ k ≤ r ^ 1 := Nat.pow_le_pow_right hr.pos hk1
        _ = r := pow_one r
    omega
  obtain ⟨s, hs, hsr, hsΦ⟩ := hex
  have hsΦ' : (s : ℤ) ∣ Φ := Int.natCast_dvd.mpr hsΦ
  refine ⟨s, hs, hsr, ?_, fun hsB => hsr ?_⟩
  · rw [eq_geomPhi_mul hε hrodd hm hA hB]
    exact hsΦ'.mul_right B
  · apply eq_of_dvd_geomPhi hε hr hr2 hs hsΦ'
    rw [← hB]
    exact hsB.mul_right m

end CFSG.Wreathed.OriginalAllPrime.IVFacts
