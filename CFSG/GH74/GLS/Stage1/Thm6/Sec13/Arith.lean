module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

theorem key_arith (n : ℕ) (hn : 1 ≤ n) (a o u e : ℕ) (ho : ¬ 2 ∣ o)
    (h : a * (8 * o) = 2 ^ e * u) (hr4 : 4 * 4 ^ n ≤ 2 ^ e) (ha : a ≤ 4 ^ n) (ha3 : a % 3 = 1)
    (ha0 : 0 < a) : a = 4 ^ n := by
  have hcop : Nat.Coprime (2 ^ e) o := by
    apply Nat.Coprime.pow_left
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 ho
  have hdvd : 2 ^ e ∣ 8 * a := by
    have : 2 ^ e ∣ (8 * a) * o := by
      have : (8 * a) * o = 2 ^ e * u := by rw [← h]; ring
      rw [this]; exact Dvd.intro _ rfl
    exact hcop.dvd_of_dvd_mul_right this
  obtain ⟨q, hq⟩ := hdvd
  have h4n : 4 ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · rw [h0] at hq; omega
    · exact h0
  have hpos : 0 < 2 ^ e := by positivity
  have hq2 : q ≤ 2 := by
    by_contra hcon
    push Not at hcon
    have : 2 ^ e * 3 ≤ 2 ^ e * q := Nat.mul_le_mul_left _ hcon
    have : 8 * a ≤ 8 * 4 ^ n := by omega
    omega
  have hn' : 2 * n + 2 ≤ e := by
    have : 2 ^ (2 * n + 2) ≤ 2 ^ e := by
      calc 2 ^ (2 * n + 2) = 4 * 4 ^ n := by rw [h4n]; ring
        _ ≤ 2 ^ e := hr4
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 3 := ⟨e - 3, by omega⟩
  have hexp : 2 ^ (e' + 3) = 8 * 2 ^ e' := by ring
  interval_cases q
  · have : a = 2 ^ e' := by rw [hexp] at hq; omega
    subst this
    have h1 : e' ≤ 2 * n := by
      have : 2 ^ e' ≤ 2 ^ (2 * n) := by rw [← h4n]; exact ha
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 this
    have h2 : 2 * n ≤ e' + 1 := by omega
    have hmod : ∀ k : ℕ, 2 ^ (2 * k) % 3 = 1 := by
      intro k
      rw [pow_mul, Nat.pow_mod]; norm_num
    have hmod2 : ∀ k : ℕ, 2 ^ (2 * k + 1) % 3 = 2 := by
      intro k
      rw [pow_succ, Nat.mul_mod, hmod k]
    rcases Nat.even_or_odd' e' with ⟨k, hk | hk⟩
    · have hkn : k = n := by omega
      rw [hk, hkn, h4n]
    · rw [hk, hmod2 k] at ha3; omega
  · have : a = 2 ^ (e' + 1) := by rw [hexp] at hq; rw [pow_succ]; omega
    subst this
    have h1 : e' + 1 ≤ 2 * n := by
      have : 2 ^ (e' + 1) ≤ 2 ^ (2 * n) := by rw [← h4n]; exact ha
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 this
    have h2 : 2 * n ≤ e' + 1 := by omega
    have : e' + 1 = 2 * n := by omega
    rw [this, h4n]

theorem key_arith2 (n e o u : ℕ) (ho : ¬ 2 ∣ o) (hu : ¬ 2 ∣ u)
    (h : 4 ^ n * (8 * o) = 2 ^ e * u) : e = 2 * n + 3 := by
  have h1 : 4 ^ n * (8 * o) = 2 ^ (2 * n + 3) * o := by
    rw [pow_add, pow_mul]; norm_num; ring
  rw [h1] at h
  rcases lt_trichotomy e (2 * n + 3) with hlt | heq | hgt
  · exfalso
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hlt
    have h3 : 2 ^ (2 * n + 3) = 2 ^ e * 2 ^ (k + 1) := by rw [hk]; ring
    rw [h3, mul_assoc] at h
    have h2 : u = 2 ^ (k + 1) * o := by
      apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ e)
      exact h.symm
    apply hu
    rw [h2]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  · exact heq
  · exfalso
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hgt
    have h3 : 2 ^ e = 2 ^ (2 * n + 3) * 2 ^ (k + 1) := by rw [hk]; ring
    rw [h3, mul_assoc] at h
    have h2 : o = 2 ^ (k + 1) * u := by
      apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ (2 * n + 3))
      exact h
    apply ho
    rw [h2]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _

theorem two_adic_unique (p q x y : ℕ) (hx : ¬ 2 ∣ x) (hy : ¬ 2 ∣ y)
    (h : 2 ^ p * x = 2 ^ q * y) : p = q := by
  rcases lt_trichotomy p q with hlt | heq | hgt
  · exfalso
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hlt
    have h3 : 2 ^ q = 2 ^ p * 2 ^ (k + 1) := by rw [hk]; ring
    rw [h3, mul_assoc] at h
    have h2 : x = 2 ^ (k + 1) * y := by
      apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ p)
      exact h
    apply hx
    rw [h2]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  · exact heq
  · exfalso
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hgt
    have h3 : 2 ^ p = 2 ^ q * 2 ^ (k + 1) := by rw [hk]; ring
    rw [h3, mul_assoc] at h
    have h2 : y = 2 ^ (k + 1) * x := by
      apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ q)
      exact h.symm
    apply hy
    rw [h2]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _

theorem pow4_cases_even (n p a a' : ℕ) (hp : p + 2 = 2 * n) (ha' : ¬ 2 ∣ a')
    (hpa : a = 2 ^ p * a') (ha : a ≤ 4 ^ n) (ha3 : a % 3 = 1) : 4 * a = 4 ^ n := by
  have h4n : 4 ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
  have hle : 2 ^ p * a' ≤ 2 ^ (2 * n) := by rw [← hpa, ← h4n]; exact ha
  have h2n : 2 ^ (2 * n) = 2 ^ p * 4 := by rw [← hp]; ring
  have ha'4 : a' ≤ 4 := by
    rw [h2n] at hle
    have : 0 < 2 ^ p := by positivity
    nlinarith
  have ha'1 : a' = 1 := by
    have : a' = 0 ∨ a' = 1 ∨ a' = 2 ∨ a' = 3 ∨ a' = 4 := by omega
    rcases this with h1 | h1 | h1 | h1 | h1
    · exact absurd (by rw [h1]; exact dvd_zero 2) ha'
    · exact h1
    · exact absurd (by rw [h1]) ha'
    · exfalso
      rw [hpa, h1] at ha3
      have : (2 ^ p * 3) % 3 = 0 := Nat.mul_mod_left _ _
      omega
    · exact absurd (by rw [h1]; norm_num) ha'
  rw [hpa, ha'1, h4n, h2n]; ring

theorem pow4_cases_odd (n p a a' : ℕ) (hp : p + 2 = 2 * n + 1) (ha' : ¬ 2 ∣ a')
    (hpa : a = 2 ^ p * a') (ha : a ≤ 4 ^ n) (ha3 : a % 3 = 1) : False := by
  have h4n : 4 ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
  have hle : 2 ^ p * a' ≤ 2 ^ (2 * n) := by rw [← hpa, ← h4n]; exact ha
  have h2n : 2 ^ (2 * n) = 2 ^ p * 2 := by
    have : 2 * n = p + 1 := by omega
    rw [this]; ring
  have ha'2 : a' ≤ 2 := by
    rw [h2n] at hle
    have : 0 < 2 ^ p := by positivity
    nlinarith
  have ha'1 : a' = 1 := by
    have : a' = 0 ∨ a' = 1 ∨ a' = 2 := by omega
    rcases this with h1 | h1 | h1
    · exact absurd (by rw [h1]; exact dvd_zero 2) ha'
    · exact h1
    · exact absurd (by rw [h1]) ha'
  have hp' : p = 2 * (n - 1) + 1 := by omega
  rw [hpa, ha'1, hp'] at ha3
  have hmod : ∀ k : ℕ, 2 ^ (2 * k) % 3 = 1 := by
    intro k; rw [pow_mul, Nat.pow_mod]; norm_num
  have hmod2 : ∀ k : ℕ, 2 ^ (2 * k + 1) % 3 = 2 := by
    intro k; rw [pow_succ, Nat.mul_mod, hmod k]
  rw [mul_one, hmod2] at ha3
  omega

theorem key_arith3 (n a o u b : ℕ) (hb : b ∣ 6) (ho : ¬ 2 ∣ o) (hu : ¬ 2 ∣ u)
    (h : a * 4 * o = 4 ^ n * u * b) (ha : a ≤ 4 ^ n) (ha3 : a % 3 = 1) (ha0 : 0 < a) :
    4 * a = 4 ^ n := by
  have hb' : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 6 := by
    have : b ∈ Nat.divisors 6 := by simpa using hb
    have h6 : Nat.divisors 6 = {1, 2, 3, 6} := by decide
    rw [h6] at this
    simpa using this
  have h4n : 4 ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
  obtain ⟨p, a', ha', hpa⟩ : ∃ p a', ¬ 2 ∣ a' ∧ a = 2 ^ p * a' :=
    Nat.exists_eq_pow_mul_and_not_dvd ha0.ne' 2 (by norm_num)
  have hao : ¬ 2 ∣ a' * o := by
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hd with h1 | h1
    · exact ha' h1
    · exact ho h1
  have h3u : ¬ 2 ∣ 3 * u := by
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hd with h1 | h1
    · omega
    · exact hu h1
  rw [h4n, hpa] at h
  have hp2 : (2 : ℕ) ^ (p + 2) = 2 ^ p * 4 := by ring
  have hq2 : (2 : ℕ) ^ (2 * n + 1) = 2 ^ (2 * n) * 2 := by ring
  rcases hb' with rfl | rfl | rfl | rfl
  · have e : 2 ^ (p + 2) * (a' * o) = 2 ^ (2 * n) * u := by
      rw [hp2]
      calc 2 ^ p * 4 * (a' * o) = 2 ^ p * a' * 4 * o := by ring
        _ = 2 ^ (2 * n) * u * 1 := h
        _ = 2 ^ (2 * n) * u := by ring
    exact pow4_cases_even n p a a' (two_adic_unique _ _ _ _ hao hu e) ha' hpa ha ha3
  · have e : 2 ^ (p + 2) * (a' * o) = 2 ^ (2 * n + 1) * u := by
      rw [hp2, hq2]
      calc 2 ^ p * 4 * (a' * o) = 2 ^ p * a' * 4 * o := by ring
        _ = 2 ^ (2 * n) * u * 2 := h
        _ = 2 ^ (2 * n) * 2 * u := by ring
    exact (pow4_cases_odd n p a a' (two_adic_unique _ _ _ _ hao hu e) ha' hpa ha ha3).elim
  · have e : 2 ^ (p + 2) * (a' * o) = 2 ^ (2 * n) * (3 * u) := by
      rw [hp2]
      calc 2 ^ p * 4 * (a' * o) = 2 ^ p * a' * 4 * o := by ring
        _ = 2 ^ (2 * n) * u * 3 := h
        _ = 2 ^ (2 * n) * (3 * u) := by ring
    exact pow4_cases_even n p a a' (two_adic_unique _ _ _ _ hao h3u e) ha' hpa ha ha3
  · have e : 2 ^ (p + 2) * (a' * o) = 2 ^ (2 * n + 1) * (3 * u) := by
      rw [hp2, hq2]
      calc 2 ^ p * 4 * (a' * o) = 2 ^ p * a' * 4 * o := by ring
        _ = 2 ^ (2 * n) * u * 6 := h
        _ = 2 ^ (2 * n) * 2 * (3 * u) := by ring
    exact (pow4_cases_odd n p a a' (two_adic_unique _ _ _ _ hao h3u e) ha' hpa ha ha3).elim

theorem para_arith (n a o u k β β' c bB mM : ℕ) (ho : ¬ 2 ∣ o) (hu : ¬ 2 ∣ u) (hβ6 : β ∣ 6)
    (hβ' : β = k * β') (hk0 : 0 < k) (N1 : a * c = bB) (N5 : β * mM = bB)
    (N6 : k * (8 * o) = c) (N4 : u * (2 * 4 ^ n) = mM) (ha : a ≤ 4 ^ n) (ha3 : a % 3 = 1)
    (ha0 : 0 < a) : 4 * a = 4 ^ n := by
  have e1 : a * (8 * o) = β' * (u * (2 * 4 ^ n)) := by
    apply Nat.eq_of_mul_eq_mul_left hk0
    calc k * (a * (8 * o)) = a * (k * (8 * o)) := by ring
      _ = a * c := by rw [N6]
      _ = bB := N1
      _ = β * mM := N5.symm
      _ = (k * β') * (u * (2 * 4 ^ n)) := by rw [hβ', ← N4]
      _ = k * (β' * (u * (2 * 4 ^ n))) := by ring
  have hβ'6 : β' ∣ 6 := (Dvd.intro_left k hβ'.symm).trans hβ6
  have e2 : 2 * (a * 4 * o) = 2 * (4 ^ n * u * β') := by
    calc 2 * (a * 4 * o) = a * (8 * o) := by ring
      _ = β' * (u * (2 * 4 ^ n)) := e1
      _ = 2 * (4 ^ n * u * β') := by ring
  have h := Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) e2
  exact key_arith3 n a o u β' hβ'6 ho hu h ha ha3 ha0

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
