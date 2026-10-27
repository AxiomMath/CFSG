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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.QuasithinUnique.I43Dihedral

private theorem two_pow_succ_dvd_sq_sub_one {x s : ℕ} (hx : Odd x)
    (h : x - 1 = 2 ^ s ∨ x + 1 = 2 ^ s) : 2 ^ (s + 1) ∣ x ^ 2 - 1 := by
  obtain ⟨t, rfl⟩ := hx
  have hsq : (2 * t + 1) ^ 2 - 1 = (2 * t) * (2 * t + 2) := by
    have h1 : (2 * t + 1) ^ 2 = 4 * t * t + 4 * t + 1 := by ring
    have h2 : (2 * t) * (2 * t + 2) = 4 * t * t + 4 * t := by ring
    omega
  rw [hsq]
  rcases h with h | h
  · have h' : 2 * t = 2 ^ s := by omega
    exact ⟨t + 1, by rw [pow_succ, ← h']; ring⟩
  · have h' : 2 * t + 2 = 2 ^ s := by omega
    exact ⟨t, by rw [pow_succ, ← h']; ring⟩

private theorem two_pow_succ_dvd_pow_odd_sub_self {x s j : ℕ} (hx : Odd x)
    (h : x - 1 = 2 ^ s ∨ x + 1 = 2 ^ s) : 2 ^ (s + 1) ∣ x ^ (2 * j + 1) - x := by
  have h1 := two_pow_succ_dvd_sq_sub_one hx h
  have h2 : x ^ 2 - 1 ∣ (x ^ 2) ^ j - 1 := by
    simpa using Nat.sub_dvd_pow_sub_pow (x ^ 2) 1 j
  have h3 : x ^ (2 * j + 1) - x = x * ((x ^ 2) ^ j - 1) := by
    rw [Nat.mul_sub, mul_one, pow_succ, pow_mul, mul_comm]
  rw [h3]
  exact (h1.trans h2).mul_left x

private theorem odd_of_primePow {p f m : ℕ} (hp : p.Prime) (hf : 0 < f) (hm : 1 ≤ m)
    (h : p ^ f = 2 ^ m + 1 ∨ p ^ f + 1 = 2 ^ m) : Odd p := by
  by_contra hodd
  have hp2 : p = 2 := by
    rcases hp.eq_two_or_odd' with h2 | h2
    · exact h2
    · exact absurd h2 hodd
  subst hp2
  have h1 : 2 ∣ 2 ^ f := dvd_pow_self 2 hf.ne'
  have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  omega

private theorem not_even_of_primePow_add_one_eq_two_pow {p f m : ℕ} (hodd : Odd p) (hm : 2 ≤ m)
    (hfe : Even f) (h : p ^ f + 1 = 2 ^ m) : False := by
  obtain ⟨g, hg⟩ := hfe
  obtain ⟨t, ht⟩ := hodd.pow (n := g)
  have hpf : p ^ f + 1 = 4 * (t * t + t) + 2 := by
    have : p ^ f = (p ^ g) ^ 2 := by rw [hg, ← two_mul, pow_mul']
    rw [this, ht]
    ring
  have h4 : 4 ∣ 2 ^ m := by
    have : 2 ^ m = 2 ^ 2 * 2 ^ (m - 2) := by rw [← pow_add]; congr 1; omega
    rw [this]
    exact Dvd.intro _ rfl
  rw [← h, hpf] at h4
  generalize t * t + t = w at h4
  omega

private theorem not_even_of_primePow_eq_two_pow_add_one {p f m : ℕ} (hp3 : 3 ≤ p) (hodd : Odd p)
    (hm : 4 ≤ m) (hf : 0 < f) (hfe : Even f) (h : p ^ f = 2 ^ m + 1) : False := by
  obtain ⟨g, hg⟩ := hfe
  have hg0 : 0 < g := by omega
  have hy3 : 3 ≤ p ^ g := le_trans hp3 (Nat.le_self_pow hg0.ne' p)
  have hyodd : Odd (p ^ g) := hodd.pow
  have hyy : p ^ g * p ^ g = 2 ^ m + 1 := by
    rw [← h, hg, ← two_mul, pow_mul', pow_two]
  generalize p ^ g = y at hy3 hyodd hyy
  have hfac : (y - 1) * (y + 1) = 2 ^ m := by
    obtain ⟨u, hu⟩ : ∃ u, y = u + 1 := ⟨y - 1, by omega⟩
    rw [hu] at hyy ⊢
    simp only [Nat.add_sub_cancel]
    nlinarith
  have hd1 : y - 1 ∣ 2 ^ m := Dvd.intro _ hfac
  have hd2 : y + 1 ∣ 2 ^ m := Dvd.intro_left _ hfac
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd1
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd2
  have h16 : 16 ≤ 2 ^ m := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hb2 : 2 ≤ b := by
    by_contra hb2
    have : 2 ^ b ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h4b : 4 ∣ 2 ^ b := by
    have : 2 ^ b = 2 ^ 2 * 2 ^ (b - 2) := by rw [← pow_add]; congr 1; omega
    rw [this]
    exact Dvd.intro _ rfl
  rcases Nat.lt_or_ge a 2 with ha2 | ha2
  · interval_cases a
    · simp at ha
      omega
    · simp at ha
      have : y = 3 := by omega
      subst this
      omega
  · have h4a : 4 ∣ 2 ^ a := by
      have : 2 ^ a = 2 ^ 2 * 2 ^ (a - 2) := by rw [← pow_add]; congr 1; omega
      rw [this]
      exact Dvd.intro _ rfl
    rw [← ha] at h4a
    rw [← hb] at h4b
    omega

theorem eq_one_of_primePow_eq_two_pow_add_one {p f m : ℕ} (hp : p.Prime) (hf : 0 < f)
    (hm : 4 ≤ m) (h : p ^ f = 2 ^ m + 1) : f = 1 := by
  have hodd : Odd p := odd_of_primePow hp hf (by omega) (Or.inl h)
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    rcases hodd with ⟨t, ht⟩
    omega
  rcases Nat.even_or_odd f with hfe | hfo
  · exact (not_even_of_primePow_eq_two_pow_add_one hp3 hodd hm hf hfe h).elim
  · obtain ⟨j, hj⟩ := hfo
    have hdvd : p - 1 ∣ 2 ^ m := by
      have := Nat.sub_dvd_pow_sub_pow p 1 f
      rw [one_pow, h] at this
      simpa using this
    obtain ⟨s, -, hs⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hdiv : 2 ^ (s + 1) ∣ p ^ f - p := by
      rw [hj]
      exact two_pow_succ_dvd_pow_odd_sub_self hodd (Or.inl hs)
    have hge : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    by_cases hsm' : s + 1 ≤ m
    · exfalso
      have h2m : 2 ^ (s + 1) ∣ 2 ^ m := Nat.pow_dvd_pow 2 hsm'
      have hsum : 2 ^ m = (p ^ f - p) + 2 ^ s := by omega
      rw [hsum] at h2m
      have h3 : 2 ^ (s + 1) ∣ 2 ^ s := (Nat.dvd_add_right hdiv).mp h2m
      have h4 := Nat.le_of_dvd (by positivity) h3
      rw [pow_succ] at h4
      have : 0 < 2 ^ s := by positivity
      omega
    · have hms : m ≤ s := by omega
      have : 2 ^ m ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hms
      have hle : p ^ f ≤ p ^ 1 := by rw [pow_one]; omega
      have := (Nat.pow_le_pow_iff_right (by omega : 1 < p)).mp hle
      omega

theorem eq_one_of_primePow_add_one_eq_two_pow {p f m : ℕ} (hp : p.Prime) (hf : 0 < f)
    (hm : 2 ≤ m) (h : p ^ f + 1 = 2 ^ m) : f = 1 := by
  have hodd : Odd p := odd_of_primePow hp hf (by omega) (Or.inr h)
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    rcases hodd with ⟨t, ht⟩
    omega
  rcases Nat.even_or_odd f with hfe | hfo
  · exact (not_even_of_primePow_add_one_eq_two_pow hodd hm hfe h).elim
  · obtain ⟨j, hj⟩ := hfo
    have hdvd : p + 1 ∣ 2 ^ m := by
      have := Odd.nat_add_dvd_pow_add_pow p 1 (⟨j, hj⟩ : Odd f)
      rw [one_pow, h] at this
      exact this
    obtain ⟨s, -, hs⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hdiv : 2 ^ (s + 1) ∣ p ^ f - p := by
      rw [hj]
      exact two_pow_succ_dvd_pow_odd_sub_self hodd (Or.inr hs)
    have hge : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    by_cases hsm' : s + 1 ≤ m
    · exfalso
      have h2m : 2 ^ (s + 1) ∣ 2 ^ m := Nat.pow_dvd_pow 2 hsm'
      have hsum : 2 ^ m = (p ^ f - p) + 2 ^ s := by omega
      rw [hsum] at h2m
      have h3 : 2 ^ (s + 1) ∣ 2 ^ s := (Nat.dvd_add_right hdiv).mp h2m
      have h4 := Nat.le_of_dvd (by positivity) h3
      rw [pow_succ] at h4
      have : 0 < 2 ^ s := by positivity
      omega
    · have hms : m ≤ s := by omega
      have : 2 ^ m ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hms
      have hle : p ^ f ≤ p ^ 1 := by rw [pow_one]; omega
      have := (Nat.pow_le_pow_iff_right (by omega : 1 < p)).mp hle
      omega

theorem fermat_or_mersenne_of_primePow {p f k : ℕ} (hp : p.Prime) (hf : 0 < f) (hk : 3 ≤ k)
    (h : p ^ f = 2 ^ (k + 1) + 1 ∨ p ^ f + 1 = 2 ^ (k + 1)) :
    f = 1 ∧ 7 < p ∧
      ((∃ j : ℕ, p = 2 ^ 2 ^ j + 1) ∨ (∃ j : ℕ, 2 ≤ j ∧ p = 2 ^ j - 1)) := by
  have h16 : 16 ≤ 2 ^ (k + 1) := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases h with h | h
  · have hf1 : f = 1 := eq_one_of_primePow_eq_two_pow_add_one hp hf (by omega) h
    subst hf1
    rw [pow_one] at h
    refine ⟨rfl, by omega, Or.inl ?_⟩
    have hprime : (2 ^ (k + 1) + 1).Prime := h ▸ hp
    obtain ⟨j, hj⟩ := Nat.pow_of_pow_add_prime (by norm_num : 1 < 2) (by omega : k + 1 ≠ 0) hprime
    exact ⟨j, by rw [h, ← hj]⟩
  · have hf1 : f = 1 := eq_one_of_primePow_add_one_eq_two_pow hp hf (by omega) h
    subst hf1
    rw [pow_one] at h
    exact ⟨rfl, by omega, Or.inr ⟨k + 1, by omega, by omega⟩⟩

end CFSG.QuasithinUnique.I43Dihedral
