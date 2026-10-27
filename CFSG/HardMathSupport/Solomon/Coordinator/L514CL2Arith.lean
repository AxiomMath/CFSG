module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

theorem l514c_arith_upper {R R' x y c e : ℕ} (hR : 4 ≤ R) (he : e ≤ 2)
    (hy : y + 1 = R ^ 2) (hc : c + 1 = R ^ 3 ∨ c = R ^ 3 + 1)
    (h : 3 * (R' * x) = e * (R ^ 3 * (y * c))) : 3 * (R' * x) ≤ 2 * R ^ 8 := by
  have hR2 : R ^ 2 ≤ R ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hc' : c ≤ R ^ 3 + 1 := by omega
  have hyc : y * c ≤ R ^ 5 := by
    have h1 : y * c ≤ y * (R ^ 3 + 1) := Nat.mul_le_mul_left _ hc'
    have h2 : R ^ 5 = (y + 1) * R ^ 3 := by rw [hy]; ring
    have h3 : y * (R ^ 3 + 1) ≤ R ^ 5 := by rw [h2]; nlinarith
    exact h1.trans h3
  rw [h]
  calc e * (R ^ 3 * (y * c)) ≤ 2 * (R ^ 3 * R ^ 5) :=
        Nat.mul_le_mul he (Nat.mul_le_mul_left _ hyc)
    _ = 2 * R ^ 8 := by ring

theorem l514c_arith_L1 {R R' x y c e : ℕ} (hR : 4 ≤ R) (he : e ≤ 2)
    (hx : x + 1 = R' ^ 2) (hy : y + 1 = R ^ 2) (hc : c + 1 = R ^ 3 ∨ c = R ^ 3 + 1)
    (h : 3 * (R' * x) = e * (R ^ 3 * (y * c))) : R' + 2 ≤ R ^ 3 := by
  by_contra hcon
  have hT : R ^ 3 ≤ R' + 1 := by omega
  have hup := l514c_arith_upper hR he hy hc h
  have hT64 : 64 ≤ R ^ 3 := by
    calc 64 = 4 ^ 3 := by norm_num
      _ ≤ R ^ 3 := Nat.pow_le_pow_left hR 3
  have h1 : 4 * R ^ 2 ≤ R ^ 3 := by
    have : R ^ 3 = R * R ^ 2 := by ring
    rw [this]; nlinarith
  have f3 : 4 * R ^ 8 ≤ (R ^ 3) ^ 3 := by
    have : R ^ 8 = (R ^ 3) ^ 2 * R ^ 2 := by ring
    have h' : (R ^ 3) ^ 3 = (R ^ 3) ^ 2 * R ^ 3 := by ring
    rw [this, h']; nlinarith [Nat.zero_le ((R ^ 3) ^ 2)]
  have hA : 3 * R ^ 3 ≤ 4 * R' := by omega
  have hR'2 : 4 ≤ R' ^ 2 := by nlinarith
  have hB : 3 * R' ^ 2 ≤ 4 * x := by omega
  have f1 : 3 * R' ^ 3 ≤ 4 * (R' * x) := by
    have : R' ^ 3 = R' * R' ^ 2 := by ring
    rw [this]; nlinarith
  have f2 : 27 * (R ^ 3) ^ 3 ≤ 64 * R' ^ 3 := by
    have := Nat.pow_le_pow_left hA 3
    calc 27 * (R ^ 3) ^ 3 = (3 * R ^ 3) ^ 3 := by ring
      _ ≤ (4 * R') ^ 3 := this
      _ = 64 * R' ^ 3 := by ring
  have hpos : 0 < (R ^ 3) ^ 3 := by positivity
  nlinarith

theorem l514c_arith_L2 {R R' x y c e : ℕ} (hR : 8 ≤ R) (he : e ≤ 2)
    (hx : x + 1 = R' ^ 2) (hy : y + 1 = R ^ 2) (hc : c + 1 = R ^ 3 ∨ c = R ^ 3 + 1)
    (h : 3 * (R' * x) = e * (R ^ 3 * (y * c))) : 2 * R' + 2 < R ^ 3 := by
  by_contra hcon
  have hT : R ^ 3 ≤ 2 * R' + 2 := by omega
  have hup := l514c_arith_upper (by omega) he hy hc h
  have hT512 : 512 ≤ R ^ 3 := by
    calc 512 = 8 ^ 3 := by norm_num
      _ ≤ R ^ 3 := Nat.pow_le_pow_left hR 3
  have h1 : 8 * R ^ 2 ≤ R ^ 3 := by
    have : R ^ 3 = R * R ^ 2 := by ring
    rw [this]; nlinarith
  have f3 : 8 * R ^ 8 ≤ (R ^ 3) ^ 3 := by
    have : R ^ 8 = (R ^ 3) ^ 2 * R ^ 2 := by ring
    have h' : (R ^ 3) ^ 3 = (R ^ 3) ^ 2 * R ^ 3 := by ring
    rw [this, h']; nlinarith [Nat.zero_le ((R ^ 3) ^ 2)]
  have hA : 49 * R ^ 3 ≤ 100 * R' := by omega
  have hR'2 : 100 ≤ R' ^ 2 := by nlinarith
  have hB : 99 * R' ^ 2 ≤ 100 * x := by omega
  have f1 : 99 * R' ^ 3 ≤ 100 * (R' * x) := by
    have : R' ^ 3 = R' * R' ^ 2 := by ring
    rw [this]; nlinarith
  have f2 : 117649 * (R ^ 3) ^ 3 ≤ 1000000 * R' ^ 3 := by
    have := Nat.pow_le_pow_left hA 3
    calc 117649 * (R ^ 3) ^ 3 = (49 * R ^ 3) ^ 3 := by ring
      _ ≤ (100 * R') ^ 3 := this
      _ = 1000000 * R' ^ 3 := by ring
  have hpos : 0 < (R ^ 3) ^ 3 := by positivity
  nlinarith


theorem l514c_arith_four {R' x c e : ℕ} (he : 1 ≤ e ∧ e ≤ 2) (hx : x + 1 = R' ^ 2)
    (hc : c = 63 ∨ c = 65) (h : 3 * (R' * x) = e * (4 ^ 3 * (15 * c))) : False := by
  have hR' : R' ≤ 40 := by
    by_contra hcon
    have h41 : 41 ≤ R' := by omega
    have : 41 * 41 ≤ R' * R' := Nat.mul_le_mul h41 h41
    have hxx : 1680 ≤ x := by nlinarith
    have : 41 * 1680 ≤ R' * x := Nat.mul_le_mul h41 hxx
    obtain ⟨he1, he2⟩ := he
    rcases hc with rfl | rfl <;> nlinarith
  obtain ⟨he1, he2⟩ := he
  obtain rfl | rfl : e = 1 ∨ e = 2 := by omega
  all_goals rcases hc with rfl | rfl
  all_goals interval_cases R' <;> (try norm_num at hx) <;> (try norm_num at h) <;> (try omega)

theorem l514c_two_adic {k m : ℕ} (hm : 1 ≤ m) (h : 2 ^ k ∣ m * (m + 1)) : 2 ^ k ≤ m + 1 := by
  have hp : Nat.Prime 2 := Nat.prime_two
  rcases Nat.even_or_odd m with he | ho
  · have hc : Nat.Coprime (2 ^ k) (m + 1) := by
      apply Nat.Coprime.pow_left
      rw [Nat.coprime_two_left]
      exact he.add_one
    have := hc.dvd_of_dvd_mul_right h
    exact (Nat.le_of_dvd (by omega) this).trans (Nat.le_succ m)
  · have hc : Nat.Coprime (2 ^ k) m := by
      apply Nat.Coprime.pow_left
      rwa [Nat.coprime_two_left]
    exact Nat.le_of_dvd (by omega) (hc.dvd_of_dvd_mul_left h)

theorem l514c_odd_adic {p n s : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hs : 1 ≤ s)
    (h : p ^ n ∣ s * (s + 2)) : p ^ n ≤ s + 2 := by
  by_cases h1 : p ∣ s
  · have h2 : ¬ p ∣ s + 2 := by
      intro h2
      have : p ∣ 2 := (Nat.dvd_add_right h1).1 h2
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
    have hc : Nat.Coprime (p ^ n) (s + 2) := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 h2)
    exact (Nat.le_of_dvd (by omega) (hc.dvd_of_dvd_mul_right h)).trans (by omega)
  · have hc : Nat.Coprime (p ^ n) s := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 h1)
    exact Nat.le_of_dvd (by omega) (hc.dvd_of_dvd_mul_left h)


theorem l514c_arith {p a p' b e x y c : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (ha : 1 ≤ a)
    (hp' : p'.Prime) (hb : 1 ≤ b) (hR : 4 ≤ p ^ a) (he : 1 ≤ e ∧ e ≤ 2)
    (hx : x + 1 = (p' ^ b) ^ 2) (hy : y + 1 = (p ^ a) ^ 2)
    (hc : c + 1 = (p ^ a) ^ 3 ∨ c = (p ^ a) ^ 3 + 1)
    (h : 3 * (p' ^ b * x) = e * ((p ^ a) ^ 3 * (y * c))) : False := by
  have hL1 := l514c_arith_L1 hR he.2 hx hy hc h
  have hR'2 : 2 ≤ p' ^ b := hp'.two_le.trans (Nat.le_self_pow (by omega) _)
  have hT : (p ^ a) ^ 3 = p ^ (3 * a) := by rw [← pow_mul, mul_comm]
  have hc3 : Nat.Coprime ((p ^ a) ^ 3) 3 :=
    Nat.Coprime.pow_left _ (Nat.Coprime.pow_left _ ((Nat.coprime_primes hp Nat.prime_three).2 hp3))
  by_cases hpp : p = p'
  · subst hpp
    have hpx : ¬ p ∣ x := by
      intro hdx
      have h1 : p ∣ x + 1 := by
        rw [hx]; exact dvd_pow (dvd_pow_self p (by omega)) (by norm_num)
      have : p ∣ 1 := (Nat.dvd_add_right hdx).1 h1
      exact hp.one_lt.ne' (Nat.dvd_one.1 this)
    have hcx : Nat.Coprime ((p ^ a) ^ 3) x :=
      Nat.Coprime.pow_left _ (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpx))
    have hd : (p ^ a) ^ 3 ∣ p ^ b * (3 * x) := ⟨e * (y * c), by
      calc p ^ b * (3 * x) = 3 * (p ^ b * x) := by ring
        _ = _ := by rw [h]; ring⟩
    have := (Nat.Coprime.mul_right hc3 hcx).dvd_of_dvd_mul_right hd
    have := Nat.le_of_dvd (by omega) this
    omega
  · have hcop : Nat.Coprime p p' := (Nat.coprime_primes hp hp').2 hpp
    have hcR' : Nat.Coprime ((p ^ a) ^ 3) (p' ^ b) :=
      Nat.Coprime.pow_left _ (Nat.Coprime.pow_left _ (Nat.Coprime.pow_right _ hcop))
    have hd : (p ^ a) ^ 3 ∣ (3 * p' ^ b) * x := ⟨e * (y * c), by
      calc (3 * p' ^ b) * x = 3 * (p' ^ b * x) := by ring
        _ = _ := by rw [h]; ring⟩
    have hdx : (p ^ a) ^ 3 ∣ x :=
      (Nat.Coprime.mul_right hc3 hcR').dvd_of_dvd_mul_left hd
    obtain ⟨s, hs⟩ : ∃ s, p' ^ b = s + 1 := ⟨p' ^ b - 1, by omega⟩
    have hxs : x = s * (s + 2) := by rw [hs] at hx; nlinarith
    have hs1 : 1 ≤ s := by omega
    rw [hxs, hT] at hdx
    by_cases hp2 : p = 2
    · subst hp2
      have hodd : Odd (p' ^ b) := (hp'.odd_of_ne_two (Ne.symm hpp)).pow
      obtain ⟨m, hm⟩ := hodd
      have hm1 : 1 ≤ m := by omega
      have hs2 : s = 2 * m := by omega
      by_cases ha2 : a = 2
      · subst ha2
        have hy' : y = 15 := by norm_num at hy; omega
        subst hy'
        apply l514c_arith_four he hx _ h
        norm_num at hc
        omega
      · have ha3 : 3 ≤ a := by
          rcases Nat.lt_or_ge a 3 with h3 | h3
          · exfalso
            interval_cases a
            · norm_num at hR
            · exact ha2 rfl
          · exact h3
        have h8 : 8 ≤ 2 ^ a := by
          calc 8 = 2 ^ 3 := by norm_num
            _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha3
        have hL2 := l514c_arith_L2 h8 he.2 hx hy hc h
        have h4 : 2 ^ (3 * a) = 4 * 2 ^ (3 * a - 2) := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
          congr 1; omega
        have hd2 : 2 ^ (3 * a - 2) ∣ m * (m + 1) := by
          rw [hs2, h4] at hdx
          have : 4 * 2 ^ (3 * a - 2) ∣ 4 * (m * (m + 1)) := by
            convert hdx using 1; ring
          exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
        have := l514c_two_adic hm1 hd2
        rw [hT, h4] at hL2
        omega
    · have := l514c_odd_adic hp hp2 hs1 hdx
      rw [← hT] at this
      omega

end CFSG.HardMathSupport.Solomon.Coordinator
