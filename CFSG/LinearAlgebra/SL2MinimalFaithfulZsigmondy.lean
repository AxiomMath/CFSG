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
public import Mathlib.NumberTheory.Multiplicity
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
public import Mathlib.Topology.Sheaves.Init

public section

open Polynomial

namespace CFSG.SL2MinimalFaithful

namespace Zsigmondy

theorem dvd_pow_sub_one_iff {a p : ℕ} (ha : 0 < a) (k : ℕ) :
    p ∣ a ^ k - 1 ↔ (a : ZMod p) ^ k = 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ ha), sub_eq_zero]
  simp

theorem natAbs_pow_sub_one {a : ℕ} (ha : 0 < a) (k : ℕ) :
    ((a : ℤ) ^ k - 1).natAbs = a ^ k - 1 := by
  have : ((a : ℤ) ^ k - 1) = ((a ^ k - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ ha)]; simp
  rw [this, Int.natAbs_natCast]

theorem isRoot_of_dvd {n p a : ℕ} (h : p ∣ ((cyclotomic n ℤ).eval (a : ℤ)).natAbs) :
    (cyclotomic n (ZMod p)).IsRoot (a : ZMod p) := by
  have he := cyclotomic.eval_apply (a : ℤ) n (Int.castRingHom (ZMod p))
  simp only [map_natCast] at he
  rw [IsRoot.def, he, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact Int.natCast_dvd.mpr h

theorem orderOf_eq_of_dvd {n p a : ℕ} [hp : Fact p.Prime] (hn : n ≠ 0)
    (h : p ∣ ((cyclotomic n ℤ).eval (a : ℤ)).natAbs) :
    ∃ e m : ℕ, ¬ p ∣ m ∧ n = p ^ e * m ∧ orderOf (a : ZMod p) = m := by
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.out.one_lt.ne'
  refine ⟨e, m, hm, rfl, ?_⟩
  have : NeZero (m : ZMod p) := ⟨by rwa [Ne, ZMod.natCast_eq_zero_iff]⟩
  exact (isRoot_cyclotomic_prime_pow_mul_iff_of_charP.mp (isRoot_of_dvd h)).eq_orderOf.symm

theorem primitive_of_orderOf {n p a : ℕ} (ha : 0 < a) (h : orderOf (a : ZMod p) = n) :
    p ∣ a ^ n - 1 ∧ ∀ k : ℕ, 0 < k → k < n → ¬ p ∣ a ^ k - 1 := by
  refine ⟨(dvd_pow_sub_one_iff ha n).mpr (h ▸ pow_orderOf_eq_one _), fun k hk hkn hpk => ?_⟩
  have := orderOf_dvd_of_pow_eq_one ((dvd_pow_sub_one_iff ha k).mp hpk)
  rw [h] at this
  exact absurd (Nat.le_of_dvd hk this) (not_le.mpr hkn)

theorem padicValNat_le_one {n p e m a : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (he : 0 < e)
    (hn : n = p ^ e * m) (hm : orderOf (a : ZMod p) = m) (hm0 : 0 < m) (ha : 1 < a) :
    padicValNat p ((cyclotomic n ℤ).eval (a : ℤ)).natAbs ≤ 1 := by
  set d := p ^ (e - 1) * m with hd_def
  have hnd : n = d * p := by
    rw [hn, hd_def, mul_right_comm, ← pow_succ, Nat.sub_add_cancel he]
  have hd0 : 0 < d := Nat.pos_of_ne_zero (mul_ne_zero (pow_ne_zero _ hp.out.ne_zero) hm0.ne')
  have hn0 : n ≠ 0 := by rw [hnd]; exact (mul_pos hd0 hp.out.pos).ne'
  have hdn : d ∈ n.properDivisors := by
    rw [Nat.mem_properDivisors, hnd]
    exact ⟨dvd_mul_right d p, lt_mul_right hd0 hp.out.one_lt⟩
  have heval := eval_dvd (x := (a : ℤ))
    (X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ hdn)
  simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_one] at heval
  have hnat : (a ^ d - 1) * ((cyclotomic n ℤ).eval (a : ℤ)).natAbs ∣ a ^ n - 1 := by
    have h := Int.natAbs_dvd_natAbs.mpr heval
    rwa [Int.natAbs_mul, natAbs_pow_sub_one (by omega), natAbs_pow_sub_one (by omega)] at h
  have h1 : 1 < a ^ d := Nat.one_lt_pow hd0.ne' ha
  have hn1 : 1 < a ^ n := Nat.one_lt_pow hn0 ha
  have hlte : padicValNat p (a ^ n - 1) = padicValNat p (a ^ d - 1) + 1 := by
    have h2 : p ∣ a ^ d - 1 := (dvd_pow_sub_one_iff (by omega) d).mpr
      (orderOf_dvd_iff_pow_eq_one.mp (hm ▸ dvd_mul_left m _))
    have h3 : ¬ p ∣ a ^ d := fun h => by
      have := Nat.dvd_sub h h2
      rw [Nat.sub_sub_self h1.le] at this
      exact hp.out.one_lt.ne' (Nat.dvd_one.mp this)
    have := padicValNat.pow_sub_pow (p := p) (x := a ^ d) (y := 1)
      (hp.out.odd_of_ne_two hp2) h1 (by simpa using h2) h3 (n := p) hp.out.ne_zero
    rwa [one_pow, ← pow_mul, ← hnd, padicValNat_self] at this
  have hΦ0 : ((cyclotomic n ℤ).eval (a : ℤ)).natAbs ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_dvd_iff] at hnat
    omega
  have hd1 : a ^ d - 1 ≠ 0 := by omega
  have hn2 : a ^ n - 1 ≠ 0 := by omega
  have hle := (padicValNat_dvd_iff_le (p := p) hn2).mp (pow_padicValNat_dvd.trans hnat)
  rw [padicValNat.mul hd1 hΦ0, hlte] at hle
  omega

theorem natAbs_cyclotomic_two_pow_eval_mod_four {a e : ℕ} (ha : a % 2 = 1) (he : 2 ≤ e) :
    ((cyclotomic (2 ^ e) ℤ).eval (a : ℤ)).natAbs % 4 = 2 := by
  obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 + 1 := ⟨e - 2, by omega⟩
  have heval : (cyclotomic (2 ^ (f + 1 + 1)) ℤ).eval (a : ℤ) =
      ((1 + a ^ 2 ^ (f + 1) : ℕ) : ℤ) := by
    rw [cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
    simp [Finset.sum_range_succ]
  obtain ⟨c, hc⟩ : ∃ c, a ^ 2 ^ f = 2 * c + 1 := ⟨a ^ 2 ^ f / 2, by
    have : a ^ 2 ^ f % 2 = 1 := Nat.odd_iff.mp (Odd.pow (Nat.odd_iff.mpr ha))
    omega⟩
  rw [heval, Int.natAbs_natCast, pow_succ (2 : ℕ) f, pow_mul, hc]
  have : 1 + (2 * c + 1) ^ 2 = 4 * (c * c + c) + 2 := by ring
  omega

theorem lt_natAbs_cyclotomic_eval {n ℓ a : ℕ} (hℓ : ℓ.Prime) (hℓn : ℓ ∣ n) (hn : 1 < n)
    (ha : 3 ≤ a) : ℓ < ((cyclotomic n ℤ).eval (a : ℤ)).natAbs := by
  have hlow := sub_one_pow_totient_lt_natAbs_cyclotomic_eval (q := a) hn (by omega)
  have h1 : ℓ - 1 ≤ n.totient := by
    have := Nat.totient_dvd_of_dvd hℓn
    rw [Nat.totient_prime hℓ] at this
    exact Nat.le_of_dvd (Nat.totient_pos.mpr (by omega)) this
  have h2 : 2 ^ n.totient ≤ (a - 1) ^ n.totient := Nat.pow_le_pow_left (by omega) _
  have h3 : 2 ^ (ℓ - 1) ≤ 2 ^ n.totient := Nat.pow_le_pow_right (by norm_num) h1
  have h4 : ℓ - 1 < 2 ^ (ℓ - 1) := Nat.lt_two_pow_self
  omega

end Zsigmondy

open Zsigmondy in
theorem exists_primitive_prime_dvd_pow_sub_one {a n : ℕ} (ha : 3 ≤ a) (hn : 3 ≤ n) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ a ^ n - 1 ∧ ∀ k : ℕ, 0 < k → k < n → ¬ ℓ ∣ a ^ k - 1 := by
  set Φ := ((cyclotomic n ℤ).eval (a : ℤ)).natAbs with hΦ
  have hΦa : a - 1 < Φ := sub_one_lt_natAbs_cyclotomic_eval (by omega) (by omega)
  by_contra hcon
  push Not at hcon
  have key : ∀ ℓ, ℓ.Prime → ℓ ∣ Φ → ∃ e m, 0 < e ∧ ¬ ℓ ∣ m ∧ n = ℓ ^ e * m ∧
      orderOf (a : ZMod ℓ) = m ∧ 0 < m ∧ m ∣ ℓ - 1 ∧ ¬ ℓ ∣ a := by
    intro ℓ hℓ hℓΦ
    have := Fact.mk hℓ
    obtain ⟨e, m, hm, hnm, hord⟩ := orderOf_eq_of_dvd (by omega) hℓΦ
    have hm0 : m ≠ 0 := by rintro rfl; omega
    have ha0 : (a : ZMod ℓ) ≠ 0 := by
      intro h0
      have h1 := pow_orderOf_eq_one (a : ZMod ℓ)
      rw [hord, h0, zero_pow hm0] at h1
      exact zero_ne_one h1
    rcases Nat.eq_zero_or_pos e with rfl | he
    · rw [pow_zero, one_mul] at hnm
      subst hnm
      obtain ⟨h1, h2⟩ := primitive_of_orderOf (by omega) hord
      obtain ⟨k, hk, hkn, hℓk⟩ := hcon ℓ hℓ h1
      exact absurd hℓk (h2 k hk hkn)
    · refine ⟨e, m, he, hm, hnm, hord, Nat.pos_of_ne_zero hm0,
        hord ▸ ZMod.orderOf_dvd_card_sub_one ha0, fun h => ha0 ?_⟩
      rwa [ZMod.natCast_eq_zero_iff]
  have hℓ : Φ.minFac.Prime := Nat.minFac_prime (by omega)
  obtain ⟨e, m, he, hm, hnm, hord, hm0, hmℓ, hℓa⟩ := key _ hℓ (Nat.minFac_dvd Φ)
  set ℓ := Φ.minFac
  have hℓn : ℓ ∣ n := hnm ▸ dvd_mul_of_dvd_left (dvd_pow_self ℓ he.ne') m
  have huniq : ∀ {q : ℕ}, q.Prime → q ∣ Φ → q = ℓ := by
    intro q hq hqΦ
    obtain ⟨e', m', he', -, hnm', -, hm0', hmq, -⟩ := key q hq hqΦ
    by_contra hqℓ
    have hqm : q ∣ m := by
      have hqn : q ∣ n := hnm' ▸ dvd_mul_of_dvd_left (dvd_pow_self q he'.ne') m'
      rw [hnm] at hqn
      rcases (Nat.Prime.dvd_mul hq).mp hqn with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hℓ).mp (hq.dvd_of_dvd_pow h)) hqℓ
      · exact h
    have hℓm' : ℓ ∣ m' := by
      rw [hnm'] at hℓn
      rcases (Nat.Prime.dvd_mul hℓ).mp hℓn with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hℓ hq).mp (hℓ.dvd_of_dvd_pow h)).symm hqℓ
      · exact h
    have h1 : q ≤ m := Nat.le_of_dvd hm0 hqm
    have h2 : m ≤ ℓ - 1 := Nat.le_of_dvd (by have := hℓ.two_le; omega) hmℓ
    have h3 : ℓ ≤ m' := Nat.le_of_dvd hm0' hℓm'
    have h4 : m' ≤ q - 1 := Nat.le_of_dvd (by have := hq.two_le; omega) hmq
    omega
  have := Fact.mk hℓ
  have hv : padicValNat ℓ Φ ≤ 1 := by
    rcases eq_or_ne ℓ 2 with h2 | h2
    ·
      rw [h2] at hmℓ hnm hℓa
      have hm1 : m = 1 := by simpa using hmℓ
      rw [hm1, mul_one] at hnm
      have he2 : 2 ≤ e := by
        by_contra h
        obtain rfl : e = 1 := by omega
        rw [pow_one] at hnm
        omega
      have h4 := natAbs_cyclotomic_two_pow_eval_mod_four (a := a) (by omega) he2
      rw [← hnm, ← hΦ] at h4
      rw [h2]
      by_contra hv
      have h5 : 2 ^ 2 ∣ Φ := (pow_dvd_pow 2 (by omega)).trans pow_padicValNat_dvd
      norm_num at h5
      omega
    · exact padicValNat_le_one h2 he hnm hord hm0 (by omega)
  have hΦℓ : Φ = ℓ := by
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd (by omega : Φ ≠ 0)
      (fun hd hdΦ => huniq hd hdΦ)
    set k := Φ.primeFactorsList.length
    have hk : padicValNat ℓ Φ = k := by rw [hpow]; exact padicValNat.prime_pow k
    have hk1 : k ≤ 1 := hk ▸ hv
    interval_cases k
    · rw [pow_zero] at hpow; omega
    · rwa [pow_one] at hpow
  have hlt : ℓ < Φ := lt_natAbs_cyclotomic_eval hℓ hℓn (by omega) ha
  omega

end CFSG.SL2MinimalFaithful
