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

namespace CFSG.HardMathSupport.Solomon.LocalBalance.AutL3Arith

theorem coprime_of_not_dvd {p n : ℕ} (hp : p.Prime) (h : ¬ p ∣ n) : Nat.Coprime p n :=
  (Nat.Prime.coprime_iff_not_dvd hp).2 h

theorem dvd_diff {ℓ u v d : ℕ} (hu : ℓ ∣ u) (hv : ℓ ∣ v) (h : v = u + d) : ℓ ∣ d := by
  subst h
  exact (Nat.dvd_add_right hu).1 hv

theorem not_dvd_sub_one {p X : ℕ} (hp : p.Prime) (hX : 1 ≤ X) (hd : p ∣ X) :
    ¬ p ∣ X - 1 := fun hh => by
  have h1 : p ∣ (X - 1) + 1 := by rwa [Nat.sub_add_cancel hX]
  exact hp.ne_one (Nat.dvd_one.1 ((Nat.dvd_add_right hh).1 h1))

theorem not_dvd_add_one {p X : ℕ} (hp : p.Prime) (hd : p ∣ X) : ¬ p ∣ X + 1 := fun hh =>
  hp.ne_one (Nat.dvd_one.1 ((Nat.dvd_add_right hd).1 hh))

theorem abs_bound {ℓ k a b c e : ℕ} (hℓ : ℓ.Prime) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (he : 0 < e)
    (hab : ℓ ∣ a → ℓ ∣ b → False) (hbc : ℓ ∣ b → ℓ ∣ c → False)
    (hac : ℓ ∣ a → ℓ ∣ c → ∃ c', c = e * c' ∧ ¬ ℓ ∣ c')
    (h : ℓ ^ k ∣ a ^ 2 * (b * c)) : ℓ ^ k ≤ e * a ^ 2 ∨ ℓ ^ k ≤ b ∨ ℓ ^ k ≤ c := by
  have cop : ∀ {n : ℕ}, ¬ ℓ ∣ n → Nat.Coprime (ℓ ^ k) n := fun hn =>
    Nat.Coprime.pow_left k (coprime_of_not_dvd hℓ hn)
  by_cases hla : ℓ ∣ a
  · have hlb : ¬ ℓ ∣ b := fun hh => hab hla hh
    by_cases hlc : ℓ ∣ c
    · obtain ⟨c', hc', hc'n⟩ := hac hla hlc
      have h1 : ℓ ^ k ∣ (a ^ 2 * e) * (b * c') := by
        have : (a ^ 2 * e) * (b * c') = a ^ 2 * (b * c) := by rw [hc']; ring
        rw [this]; exact h
      have hcop : Nat.Coprime (ℓ ^ k) (b * c') :=
        Nat.Coprime.mul_right (cop hlb) (cop hc'n)
      have h2 := hcop.dvd_of_dvd_mul_right h1
      left
      calc ℓ ^ k ≤ a ^ 2 * e := Nat.le_of_dvd (by positivity) h2
        _ = e * a ^ 2 := mul_comm _ _
    · have hcop : Nat.Coprime (ℓ ^ k) (b * c) := Nat.Coprime.mul_right (cop hlb) (cop hlc)
      have h2 := hcop.dvd_of_dvd_mul_right h
      left
      calc ℓ ^ k ≤ a ^ 2 := Nat.le_of_dvd (by positivity) h2
        _ ≤ e * a ^ 2 := Nat.le_mul_of_pos_left _ he
  · have h1 : ℓ ^ k ∣ b * c :=
      (cop (fun hh => hla (hℓ.dvd_of_dvd_pow hh))).dvd_of_dvd_mul_left h
    by_cases hlb : ℓ ∣ b
    · have hlc : ¬ ℓ ∣ c := fun hh => hbc hlb hh
      have h2 := (cop hlc).dvd_of_dvd_mul_right h1
      right; left; exact Nat.le_of_dvd hb h2
    · have h2 := (cop hlb).dvd_of_dvd_mul_left h1
      right; right; exact Nat.le_of_dvd hc h2

theorem dvd_Z_t {ℓ t : ℕ} (h : ℓ ∣ t) (hc : ℓ ∣ t ^ 2 + 3 * t + 3) : ℓ ∣ 3 := by
  have e : t ^ 2 + 3 * t + 3 = t * (t + 3) + 3 := by ring
  rw [e] at hc
  exact (Nat.dvd_add_right (Dvd.dvd.mul_right h _)).1 hc

theorem dvd_Z_t3 {ℓ t : ℕ} (h : ℓ ∣ t + 3) (hc : ℓ ∣ t ^ 2 + 3 * t + 3) : ℓ ∣ 3 := by
  have e : t ^ 2 + 3 * t + 3 = (t + 3) * t + 3 := by ring
  rw [e] at hc
  exact (Nat.dvd_add_right (Dvd.dvd.mul_right h _)).1 hc

theorem dvd_Z_t2 {ℓ t : ℕ} (h : ℓ ∣ t + 2) (hc : ℓ ∣ t ^ 2 + 3 * t + 3) : ℓ ∣ 1 := by
  have e : t ^ 2 + 3 * t + 3 = (t + 2) * (t + 1) + 1 := by ring
  rw [e] at hc
  exact (Nat.dvd_add_right (Dvd.dvd.mul_right h _)).1 hc

theorem dvd_Z_t1 {ℓ t : ℕ} (h : ℓ ∣ t + 1) (hc : ℓ ∣ t ^ 2 + 3 * t + 3) : ℓ ∣ 1 := by
  have e : t ^ 2 + 3 * t + 3 = (t + 1) * (t + 2) + 1 := by ring
  rw [e] at hc
  exact (Nat.dvd_add_right (Dvd.dvd.mul_right h _)).1 hc

theorem bndZ {ℓ k t a b : ℕ} (hℓ : ℓ.Prime) (ha : 0 < a)
    (hab : (a = t ∧ b = t + 2) ∨ (a = t + 3 ∧ b = t + 1))
    (h : ℓ ^ k ∣ a ^ 2 * (b * (t ^ 2 + 3 * t + 3))) : ℓ ^ k ≤ 4 * (t + 3) ^ 2 := by
  have hb : 0 < b := by omega
  have hc : 0 < t ^ 2 + 3 * t + 3 := by positivity
  have hat : a ≤ t + 3 := by omega
  have hbt : b ≤ t + 3 := by omega
  have e1 : a ^ 2 ≤ (t + 3) ^ 2 := Nat.pow_le_pow_left hat 2
  have hZ : t ^ 2 + 3 * t + 3 ≤ 4 * (t + 3) ^ 2 := by nlinarith
  have hb3 : b ≤ (t + 3) ^ 2 := le_trans hbt (Nat.le_self_pow (by norm_num) (t + 3))
  by_cases h2 : ℓ = 2
  · subst h2
    have hc2 : (t ^ 2 + 3 * t + 3) % 2 = 1 := by
      rcases Nat.even_or_odd' t with ⟨m, hm | hm⟩
      · have : t ^ 2 + 3 * t + 3 = 2 * (2 * m ^ 2 + 3 * m + 1) + 1 := by rw [hm]; ring
        omega
      · have : t ^ 2 + 3 * t + 3 = 2 * (2 * m ^ 2 + 5 * m + 3) + 1 := by rw [hm]; ring
        omega
    have h1 : 2 ^ k ∣ a ^ 2 * b :=
      (Nat.Coprime.pow_left k (coprime_of_not_dvd (n := t ^ 2 + 3 * t + 3) Nat.prime_two
        (by omega))).dvd_of_dvd_mul_right (by rwa [← mul_assoc] at h)
    have hpar : a % 2 = b % 2 := by omega
    by_cases hao : a % 2 = 1
    · have hn : Nat.Coprime (2 ^ k) (a ^ 2 * b) := by
        refine Nat.Coprime.pow_left k (coprime_of_not_dvd Nat.prime_two fun hh => ?_)
        rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hh with h3 | h3
        · have := Nat.prime_two.dvd_of_dvd_pow h3
          omega
        · omega
      have := Nat.Coprime.eq_one_of_dvd hn h1
      rw [this]
      exact Nat.succ_le_of_lt (by positivity)
    · obtain ⟨m, hm⟩ : ∃ m, a = 2 * m := ⟨a / 2, by omega⟩
      obtain ⟨n, hn⟩ : ∃ n, b = 2 * n := ⟨b / 2, by omega⟩
      have hmn : m = n + 1 ∨ n = m + 1 := by omega
      have hfac : a ^ 2 * b = 8 * (m ^ 2 * n) := by rw [hm, hn]; ring
      rw [hfac] at h1
      by_cases hmo : m % 2 = 1
      · have hm2 : m ^ 2 % 2 = 1 := by rw [Nat.pow_mod]; simp [hmo]
        have h4 : 2 ^ k ∣ m ^ 2 * (8 * n) := by
          have : m ^ 2 * (8 * n) = 8 * (m ^ 2 * n) := by ring
          rw [this]; exact h1
        have h5 : 2 ^ k ∣ 8 * n :=
          (Nat.Coprime.pow_left k (coprime_of_not_dvd Nat.prime_two (by omega))).dvd_of_dvd_mul_left
            h4
        have := Nat.le_of_dvd (by omega) h5
        omega
      · have h4 : 2 ^ k ∣ (8 * m ^ 2) * n := by
          have : (8 * m ^ 2) * n = 8 * (m ^ 2 * n) := by ring
          rw [this]; exact h1
        have h5 : 2 ^ k ∣ 8 * m ^ 2 :=
          (Nat.Coprime.pow_left k (coprime_of_not_dvd Nat.prime_two (by omega))).dvd_of_dvd_mul_right
            h4
        have := Nat.le_of_dvd (by
          have : 0 < m := by omega
          positivity) h5
        have ham : a ^ 2 = 4 * m ^ 2 := by rw [hm]; ring
        omega
  by_cases h3 : ℓ = 3
  · subst h3
    have hab' : 3 ∣ a → 3 ∣ b → False := by
      intro h1 h2'
      rcases hab with ⟨ha', hb'⟩ | ⟨ha', hb'⟩ <;> omega
    have hbc : 3 ∣ b → 3 ∣ t ^ 2 + 3 * t + 3 → False := by
      intro h1 h2'
      rcases hab with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
      · obtain ⟨n, hn⟩ : ∃ n, t = 3 * n + 1 := ⟨t / 3, by omega⟩
        rw [hn] at h2'
        have : (3 * n + 1) ^ 2 + 3 * (3 * n + 1) + 3 = 3 * (3 * n ^ 2 + 5 * n + 2) + 1 := by ring
        rw [this] at h2'
        omega
      · obtain ⟨n, hn⟩ : ∃ n, t = 3 * n + 2 := ⟨t / 3, by omega⟩
        rw [hn] at h2'
        have : (3 * n + 2) ^ 2 + 3 * (3 * n + 2) + 3 = 3 * (3 * n ^ 2 + 7 * n + 4) + 1 := by ring
        rw [this] at h2'
        omega
    have hac : 3 ∣ a → 3 ∣ t ^ 2 + 3 * t + 3 → ∃ c', t ^ 2 + 3 * t + 3 = 3 * c' ∧ ¬ 3 ∣ c' := by
      intro h1 _
      obtain ⟨n, hn⟩ : ∃ n, t = 3 * n := by
        rcases hab with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
        · exact ⟨t / 3, by omega⟩
        · exact ⟨t / 3, by omega⟩
      refine ⟨3 * n ^ 2 + 3 * n + 1, ?_, by omega⟩
      rw [hn]; ring
    rcases abs_bound hℓ ha hb hc (by norm_num) hab' hbc hac h with h6 | h6 | h6 <;> omega
  · have hd2 : ¬ ℓ ∣ 2 := fun hh => h2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 hh)
    have hd3 : ¬ ℓ ∣ 3 := fun hh => h3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 hh)
    have hd1 : ¬ ℓ ∣ 1 := fun hh => hℓ.ne_one (Nat.dvd_one.1 hh)
    have hab' : ℓ ∣ a → ℓ ∣ b → False := by
      intro h1 h2'
      rcases hab with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
      · rw [ha'] at h1; rw [hb'] at h2'
        exact hd2 (dvd_diff h1 h2' rfl)
      · rw [ha'] at h1; rw [hb'] at h2'
        exact hd2 (dvd_diff h2' h1 (by omega))
    have hbc : ℓ ∣ b → ℓ ∣ t ^ 2 + 3 * t + 3 → False := by
      intro h1 h2'
      rcases hab with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
      · rw [hb'] at h1; exact hd1 (dvd_Z_t2 h1 h2')
      · rw [hb'] at h1; exact hd1 (dvd_Z_t1 h1 h2')
    have hac : ℓ ∣ a → ℓ ∣ t ^ 2 + 3 * t + 3 →
        ∃ c', t ^ 2 + 3 * t + 3 = 1 * c' ∧ ¬ ℓ ∣ c' := by
      intro h1 h2'
      exfalso
      rcases hab with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
      · rw [ha'] at h1; exact hd3 (dvd_Z_t h1 h2')
      · rw [ha'] at h1; exact hd3 (dvd_Z_t3 h1 h2')
    rcases abs_bound hℓ ha hb hc (by norm_num) hab' hbc hac h with h6 | h6 | h6 <;> omega

theorem exp_eq_of_mul_eq {p s t m n : ℕ} (hp : p.Prime) (hm : Nat.Coprime p m)
    (hn : Nat.Coprime p n) (h : p ^ s * m = p ^ t * n) : s = t := by
  have key : ∀ {s t m n : ℕ}, Nat.Coprime p m → p ^ s * m = p ^ t * n → s < t → False := by
    intro s t m n hm h hlt
    obtain ⟨d, rfl⟩ : ∃ d, t = s + (d + 1) := ⟨t - s - 1, by omega⟩
    have h' : p ^ s * m = p ^ s * (p ^ (d + 1) * n) := by rw [h]; ring
    have h2 := Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos s) h'
    have hdvd : p ∣ m := by
      rw [h2]; exact Dvd.dvd.mul_right (dvd_pow_self p (Nat.succ_ne_zero d)) n
    exact hp.ne_one (Nat.Coprime.eq_one_of_dvd hm hdvd)
  rcases lt_trichotomy s t with hlt | heq | hgt
  · exact (key hm h hlt).elim
  · exact heq
  · exact (key hn h.symm hgt).elim

theorem cop_pow_sub {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (n : ℕ) (hn : n ≠ 0) :
    Nat.Coprime p ((p ^ a) ^ n - 1) :=
  coprime_of_not_dvd hp (not_dvd_sub_one hp
    (Nat.pos_of_ne_zero (pow_ne_zero _ (pow_ne_zero _ hp.ne_zero)))
    (dvd_pow (dvd_pow_self p (by omega)) hn))

theorem cop_pow_add {p b : ℕ} (hp : p.Prime) (hb : 1 ≤ b) (n : ℕ) (hn : n ≠ 0) :
    Nat.Coprime p ((p ^ b) ^ n + 1) :=
  coprime_of_not_dvd hp (not_dvd_add_one hp (dvd_pow (dvd_pow_self p (by omega)) hn))

theorem core_eq {p a b g1 g2 : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hg1 : Nat.Coprime p g1) (hg2 : Nat.Coprime p g2) (hg1' : g1 ∣ 3) (hg2' : g2 ∣ 3)
    (h : g2 * ((p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 - 1))) =
      g1 * ((p ^ b) ^ 3 * (((p ^ b) ^ 2 - 1) * ((p ^ b) ^ 3 + 1)))) : False := by
  have hE : Nat.Coprime p (g2 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 - 1))) :=
    Nat.Coprime.mul_right hg2
      (Nat.Coprime.mul_right (cop_pow_sub hp ha 2 (by norm_num)) (cop_pow_sub hp ha 3 (by norm_num)))
  have hF : Nat.Coprime p (g1 * (((p ^ b) ^ 2 - 1) * ((p ^ b) ^ 3 + 1))) :=
    Nat.Coprime.mul_right hg1
      (Nat.Coprime.mul_right (cop_pow_sub hp hb 2 (by norm_num)) (cop_pow_add hp hb 3 (by norm_num)))
  have h1 : p ^ (a * 3) * (g2 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 - 1))) =
      p ^ (b * 3) * (g1 * (((p ^ b) ^ 2 - 1) * ((p ^ b) ^ 3 + 1))) := by
    calc _ = g2 * ((p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 - 1))) := by ring
      _ = g1 * ((p ^ b) ^ 3 * (((p ^ b) ^ 2 - 1) * ((p ^ b) ^ 3 + 1))) := h
      _ = _ := by ring
  have hexp : a = b := by
    have := exp_eq_of_mul_eq hp hE hF h1
    omega
  subst hexp
  have hq : 2 ≤ p ^ a := by
    have := Nat.one_lt_pow (by omega : a ≠ 0) hp.one_lt
    omega
  have hU : 8 ≤ (p ^ a) ^ 3 := by
    have := Nat.pow_le_pow_left hq 3
    norm_num at this
    exact this
  have hS : 0 < (p ^ a) ^ 2 - 1 := by
    have := Nat.pow_le_pow_left hq 2
    norm_num at this
    omega
  have hUS : 0 < (p ^ a) ^ 3 * ((p ^ a) ^ 2 - 1) := Nat.mul_pos (by omega) hS
  have h3 : g2 * ((p ^ a) ^ 3 - 1) = g1 * ((p ^ a) ^ 3 + 1) := by
    apply Nat.eq_of_mul_eq_mul_left hUS
    calc _ = g2 * ((p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 - 1))) := by ring
      _ = g1 * ((p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 + 1))) := h
      _ = _ := by ring
  clear h h1 hE hF hUS
  rcases (Nat.dvd_prime Nat.prime_three).1 hg1' with rfl | rfl <;>
    rcases (Nat.dvd_prime Nat.prime_three).1 hg2' with rfl | rfl <;> omega

theorem core_ne {p ℓ a b g1 g2 : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hpl : p ≠ ℓ) (hg1 : Nat.Coprime (p ^ a) g1) (hg2 : Nat.Coprime (ℓ ^ b) g2)
    (h : g2 * ((p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 - 1))) =
      g1 * ((ℓ ^ b) ^ 3 * (((ℓ ^ b) ^ 2 - 1) * ((ℓ ^ b) ^ 3 + 1)))) :
    (ℓ ^ b) ^ 3 ≤ 4 * (p ^ a + 2) ^ 2 ∧ (p ^ a) ^ 3 ≤ 4 * (ℓ ^ b + 1) ^ 2 := by
  have hcop : Nat.Coprime ((p ^ a) ^ 3) ((ℓ ^ b) ^ 3) :=
    Nat.Coprime.pow 3 3 (Nat.Coprime.pow a b ((Nat.coprime_primes hp hℓ).2 hpl))
  have hpa : 2 ≤ p ^ a := by
    have := Nat.one_lt_pow (by omega : a ≠ 0) hp.one_lt
    omega
  have hlb : 2 ≤ ℓ ^ b := by
    have := Nat.one_lt_pow (by omega : b ≠ 0) hℓ.one_lt
    omega
  obtain ⟨x, hx⟩ : ∃ x, p ^ a = x + 1 := ⟨p ^ a - 1, by omega⟩
  obtain ⟨w, hw⟩ : ∃ w, ℓ ^ b = w + 2 := ⟨ℓ ^ b - 2, by omega⟩
  constructor
  · have hd : (ℓ ^ b) ^ 3 ∣ g2 * ((p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 - 1))) :=
      ⟨g1 * (((ℓ ^ b) ^ 2 - 1) * ((ℓ ^ b) ^ 3 + 1)), by rw [h]; ring⟩
    have hc : Nat.Coprime ((ℓ ^ b) ^ 3) (g2 * (p ^ a) ^ 3) :=
      Nat.Coprime.mul_right (Nat.Coprime.pow_left 3 hg2) hcop.symm
    have hE : (ℓ ^ b) ^ 3 ∣ ((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 - 1) :=
      hc.dvd_of_dvd_mul_left (by rwa [← mul_assoc] at hd)
    rw [hx] at hE
    have e1 : (x + 1) ^ 2 - 1 = x * (x + 2) := Nat.sub_eq_of_eq_add (by ring)
    have e2 : (x + 1) ^ 3 - 1 = x * (x ^ 2 + 3 * x + 3) := Nat.sub_eq_of_eq_add (by ring)
    have e : ((x + 1) ^ 2 - 1) * ((x + 1) ^ 3 - 1) = x ^ 2 * ((x + 2) * (x ^ 2 + 3 * x + 3)) := by
      rw [e1, e2]; ring
    rw [e] at hE
    have hx0 : 0 < x := by omega
    have := bndZ (ℓ := ℓ) (k := b * 3) (t := x) (a := x) (b := x + 2) hℓ hx0 (Or.inl ⟨rfl, rfl⟩)
      (by rw [pow_mul]; exact hE)
    calc (ℓ ^ b) ^ 3 = ℓ ^ (b * 3) := (pow_mul ℓ b 3).symm
      _ ≤ 4 * (x + 3) ^ 2 := this
      _ = 4 * (p ^ a + 2) ^ 2 := by rw [hx]
  · have hd : (p ^ a) ^ 3 ∣ g1 * ((ℓ ^ b) ^ 3 * (((ℓ ^ b) ^ 2 - 1) * ((ℓ ^ b) ^ 3 + 1))) :=
      ⟨g2 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 - 1)), by rw [← h]; ring⟩
    have hc : Nat.Coprime ((p ^ a) ^ 3) (g1 * (ℓ ^ b) ^ 3) :=
      Nat.Coprime.mul_right (Nat.Coprime.pow_left 3 hg1) hcop
    have hF : (p ^ a) ^ 3 ∣ ((ℓ ^ b) ^ 2 - 1) * ((ℓ ^ b) ^ 3 + 1) :=
      hc.dvd_of_dvd_mul_left (by rwa [← mul_assoc] at hd)
    rw [hw] at hF
    have e1 : (w + 2) ^ 2 - 1 = (w + 1) * (w + 3) := Nat.sub_eq_of_eq_add (by ring)
    have e : ((w + 2) ^ 2 - 1) * ((w + 2) ^ 3 + 1) =
        (w + 3) ^ 2 * ((w + 1) * (w ^ 2 + 3 * w + 3)) := by
      rw [e1]; ring
    rw [e] at hF
    have := bndZ (ℓ := p) (k := a * 3) (t := w) (a := w + 3) (b := w + 1) hp (by omega)
      (Or.inr ⟨rfl, rfl⟩) (by rw [pow_mul]; exact hF)
    calc (p ^ a) ^ 3 = p ^ (a * 3) := (pow_mul p a 3).symm
      _ ≤ 4 * (w + 3) ^ 2 := this
      _ = 4 * (ℓ ^ b + 1) ^ 2 := by rw [hw]

theorem finite_check (q q' : ℕ) (hq : 2 ≤ q) (hq6 : q ≤ 6) (hq' : 2 ≤ q') (hq'6 : q' ≤ 6) :
    Nat.gcd 3 (q' + 1) * (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) ≠
      Nat.gcd 3 (q - 1) * (q' ^ 3 * ((q' ^ 2 - 1) * (q' ^ 3 + 1))) := by
  interval_cases q <;> interval_cases q' <;> decide

theorem finish (q q' : ℕ) (hq : 2 ≤ q) (hq' : 2 ≤ q') (h1 : q' ^ 3 ≤ 4 * (q + 2) ^ 2)
    (h2 : q ^ 3 ≤ 4 * (q' + 1) ^ 2) :
    Nat.gcd 3 (q' + 1) * (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) ≠
      Nat.gcd 3 (q - 1) * (q' ^ 3 * ((q' ^ 2 - 1) * (q' ^ 3 + 1))) := by
  have h6 : q ≤ 6 ∧ q' ≤ 6 := by
    rcases le_total q q' with hle | hle
    · have : q' ≤ 6 := by
        by_contra hc
        have hc : 7 ≤ q' := by omega
        have h3 : (q + 2) ^ 2 ≤ (q' + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        have h4 : 7 * q' ≤ q' * q' := Nat.mul_le_mul_right q' hc
        have h5 : q' * q' ≤ q' * q' := le_refl _
        have h7 : 7 * q' ^ 2 ≤ q' ^ 3 := by
          calc 7 * q' ^ 2 ≤ q' * q' ^ 2 := Nat.mul_le_mul_right _ hc
            _ = q' ^ 3 := by ring
        nlinarith
      omega
    · have : q ≤ 5 := by
        by_contra hc
        have hc : 6 ≤ q := by omega
        have h3 : (q' + 1) ^ 2 ≤ (q + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        have h4 : 6 * q ≤ q * q := Nat.mul_le_mul_right q hc
        have h7 : 6 * q ^ 2 ≤ q ^ 3 := by
          calc 6 * q ^ 2 ≤ q * q ^ 2 := Nat.mul_le_mul_right _ hc
            _ = q ^ 3 := by ring
        nlinarith
      omega
  exact finite_check q q' hq h6.1 hq' h6.2

theorem order_psl3_ne_psu3 {p ℓ a b : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Nat.gcd 3 (ℓ ^ b + 1) * ((p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 - 1))) ≠
      Nat.gcd 3 (p ^ a - 1) * ((ℓ ^ b) ^ 3 * (((ℓ ^ b) ^ 2 - 1) * ((ℓ ^ b) ^ 3 + 1))) := by
  intro h
  have hpa : 2 ≤ p ^ a := by
    have := Nat.one_lt_pow (by omega : a ≠ 0) hp.one_lt
    omega
  have hlb : 2 ≤ ℓ ^ b := by
    have := Nat.one_lt_pow (by omega : b ≠ 0) hℓ.one_lt
    omega
  have hg1c : Nat.Coprime p (Nat.gcd 3 (p ^ a - 1)) :=
    coprime_of_not_dvd hp fun hh =>
      not_dvd_sub_one hp (by omega) (dvd_pow_self p (by omega))
        (hh.trans (Nat.gcd_dvd_right 3 _))
  have hg2c : Nat.Coprime ℓ (Nat.gcd 3 (ℓ ^ b + 1)) :=
    coprime_of_not_dvd hℓ fun hh =>
      not_dvd_add_one hℓ (dvd_pow_self ℓ (by omega)) (hh.trans (Nat.gcd_dvd_right 3 _))
  by_cases hpl : p = ℓ
  · subst hpl
    exact core_eq hp ha hb hg1c hg2c (Nat.gcd_dvd_left 3 _) (Nat.gcd_dvd_left 3 _) h
  · obtain ⟨h1, h2⟩ := core_ne hp hℓ ha hb hpl (Nat.Coprime.pow_left a hg1c)
      (Nat.Coprime.pow_left b hg2c) h
    exact finish (p ^ a) (ℓ ^ b) hpa hlb h1 h2 h

end CFSG.HardMathSupport.Solomon.LocalBalance.AutL3Arith
