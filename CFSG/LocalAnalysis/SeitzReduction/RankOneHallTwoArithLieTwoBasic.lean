module

public import CFSG.Timmesfeld.Orders.Bang
public import Mathlib.Data.Int.Star

public section

namespace CFSG.SeitzReduction.RankOne.LieTwo

open CFSG.Timmesfeld

theorem dvd_sub_one_of_isPrimitivePrimeDivisor {r K : ℕ} (hr : IsPrimitivePrimeDivisor r K)
    (hK : 0 < K) : K ∣ r - 1 := by
  have hp := hr.prime
  have hcop : Nat.Coprime 2 r := (Nat.coprime_primes Nat.prime_two hp).2 (hr.ne_two hK).symm
  have h1 : 2 ^ (r - 1) ≡ 1 [MOD r] := Nat.ModEq.pow_card_sub_one_eq_one hp hcop
  have h2 : r ∣ 2 ^ (r - 1) - 1 := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).1 h1.symm
  exact (hr.dvd_sub_one_iff hK (r - 1)).1 h2

theorem lt_of_isPrimitivePrimeDivisor {r K : ℕ} (hr : IsPrimitivePrimeDivisor r K)
    (hK : 0 < K) : K < r := by
  have h2 := hr.prime.two_le
  have h := Nat.le_of_dvd (by omega) (dvd_sub_one_of_isPrimitivePrimeDivisor hr hK)
  omega

theorem ppd_dvd_pow_sub_one_iff {r K : ℕ} (hr : IsPrimitivePrimeDivisor r K) (hK : 0 < K)
    (f a : ℕ) : r ∣ (2 ^ f) ^ a - 1 ↔ K ∣ f * a := by
  rw [← pow_mul]
  exact hr.dvd_sub_one_iff hK _

theorem ppd_dvd_pow_sub_one {r f k a : ℕ} (hr : IsPrimitivePrimeDivisor r (f * k))
    (hka : k ∣ a) : r ∣ (2 ^ f) ^ a - 1 := by
  rw [← pow_mul]
  exact hr.dvd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 (Nat.mul_dvd_mul_left f hka))

theorem ppd_dvd_pow_add_one {r f a : ℕ} (hr : IsPrimitivePrimeDivisor r (f * (2 * a)))
    (hfa : 0 < f * a) : r ∣ (2 ^ f) ^ a + 1 := by
  have hK : f * (2 * a) = 2 * (f * a) := by ring
  rw [← pow_mul]
  refine (hr.dvd_add_one_iff (by omega) _).2 ⟨by rw [hK], fun h => ?_⟩
  have := Nat.le_of_dvd hfa h
  omega

theorem ppd_dvd_left {r f k h g j : ℕ} (hr : IsPrimitivePrimeDivisor r (f * k))
    (hfk : 0 < f * k) (hg : g ∣ (2 ^ f) ^ j - 1) (hkj : ¬ k ∣ j) (hrhg : r ∣ h * g) : r ∣ h := by
  rcases hr.prime.dvd_mul.1 hrhg with h1 | h1
  · exact h1
  · have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hfk)
    exact absurd (Nat.dvd_of_mul_dvd_mul_left hf
      ((ppd_dvd_pow_sub_one_iff hr hfk f j).1 (h1.trans hg))) hkj

theorem not_dvd_of_ppd {f k N h e r : ℕ} (hfk : 0 < f * k)
    (hr : IsPrimitivePrimeDivisor r (f * k)) (he : e = f * N) (hkN : ¬ k ∣ N)
    (hrN : ¬ r ∣ N) (hrh : r ∣ h) : ¬ h ∣ (2 ^ e - 1) * e := by
  intro hdiv
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hfk)
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hfk)
  have hlt := lt_of_isPrimitivePrimeDivisor hr hfk
  rcases hr.prime.dvd_mul.1 (hrh.trans hdiv) with h1 | h1
  · rw [hr.dvd_sub_one_iff hfk, he] at h1
    exact hkN (Nat.dvd_of_mul_dvd_mul_left hf h1)
  · rw [he] at h1
    rcases hr.prime.dvd_mul.1 h1 with h2 | h2
    · have h3 := Nat.le_of_dvd hf h2
      have h4 : f ≤ f * k := Nat.le_mul_of_pos_right f hk
      omega
    · exact hrN h2

theorem false_of_ppd {f k N h e : ℕ} (hk : 2 ≤ f * k) (h6 : f * k ≠ 6) (he : e = f * N)
    (hkN : ¬ k ∣ N) (hh : ∀ r, IsPrimitivePrimeDivisor r (f * k) → r ∣ h)
    (hN : ∀ r, IsPrimitivePrimeDivisor r (f * k) → ¬ r ∣ N)
    (hdiv : h ∣ (2 ^ e - 1) * e) : False := by
  obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor hk h6
  exact not_dvd_of_ppd (by omega) hr he hkN (hN r hr) (hh r hr) hdiv

theorem prime_le_of_dvd_mul_sub_one {r m : ℕ} (hr : r.Prime) (hm : 2 ≤ m)
    (h : r ∣ m * (m - 1)) : r ≤ m := by
  rcases hr.dvd_mul.1 h with h1 | h1
  · exact Nat.le_of_dvd (by omega) h1
  · exact (Nat.le_of_dvd (by omega) h1).trans (Nat.sub_le m 1)

theorem two_mul_tri (m : ℕ) : 2 * (m * (m - 1) / 2) = m * (m - 1) :=
  Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self m)

theorem tri_dvd (m : ℕ) : m * (m - 1) / 2 ∣ m * (m - 1) :=
  ⟨2, by rw [mul_comm (m * (m - 1) / 2) 2, two_mul_tri]⟩

theorem not_dvd_mul_sub_one {r m : ℕ} (hr : r.Prime) (hm : 2 ≤ m) (hrm : m < r) :
    ¬ r ∣ m * (m - 1) := fun h => absurd (prime_le_of_dvd_mul_sub_one hr hm h) (by omega)

theorem not_dvd_tri {r m : ℕ} (hr : r.Prime) (hm : 2 ≤ m) (hrm : m < r) :
    ¬ r ∣ m * (m - 1) / 2 := fun h => not_dvd_mul_sub_one hr hm hrm (h.trans (tri_dvd m))

theorem not_dvd_sq {r m : ℕ} (hr : r.Prime) (hm : 1 ≤ m) (hrm : m < r) : ¬ r ∣ m ^ 2 :=
  fun h => absurd (Nat.le_of_dvd (by omega) (hr.dvd_of_dvd_pow h)) (by omega)

theorem not_dvd_prod_of_primes {r : ℕ} (hr : r.Prime) :
    ∀ L : List ℕ, (∀ p ∈ L, p.Prime ∧ p ≠ r) → ¬ r ∣ L.prod
  | [], _, h => hr.one_lt.ne' (Nat.dvd_one.1 h)
  | p :: L, hL, h => by
    rw [List.prod_cons] at h
    rcases hr.dvd_mul.1 h with h1 | h1
    · obtain ⟨hp, hpr⟩ := hL p List.mem_cons_self
      exact hpr ((Nat.prime_dvd_prime_iff_eq hr hp).1 h1).symm
    · exact not_dvd_prod_of_primes hr L (fun q hq => hL q (List.mem_cons_of_mem p hq)) h1

theorem gcd_two_pow_eq_one {a x : ℕ} (hx : Odd x) : Nat.gcd (2 ^ a) x = 1 :=
  Nat.Coprime.pow_left a (Nat.coprime_two_left.2 hx)

theorem odd_two_pow_pow_sub_one {f a : ℕ} (hf : 1 ≤ f) (ha : 1 ≤ a) :
    Odd ((2 ^ f) ^ a - 1) := by
  rw [← pow_mul]
  exact Nat.Even.sub_odd Nat.one_le_two_pow
    ((Nat.even_pow' (Nat.mul_pos (by omega) (by omega)).ne').2 even_two) odd_one

theorem odd_two_pow_pow_add_one {f a : ℕ} (hf : 1 ≤ f) (ha : 1 ≤ a) :
    Odd ((2 ^ f) ^ a + 1) := by
  rw [← pow_mul]
  exact ((Nat.even_pow' (Nat.mul_pos (by omega) (by omega)).ne').2 even_two).add_one

theorem succ_dvd_sq_sub_one (q : ℕ) : q + 1 ∣ q ^ 2 - 1 :=
  ⟨q - 1, by rw [← one_pow 2, Nat.sq_sub_sq, one_pow]⟩

theorem two_pow_mul_le_pow {f a : ℕ} (hf : 1 ≤ f) (ha : 1 ≤ a) : 2 ^ a * f ≤ (2 ^ f) ^ a := by
  have h1 : f ≤ 2 ^ (f - 1) := by
    have := @Nat.lt_two_pow_self (f - 1)
    omega
  have h2 : a + (f - 1) ≤ f * a := by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    nlinarith
  calc 2 ^ a * f ≤ 2 ^ a * 2 ^ (f - 1) := Nat.mul_le_mul_left _ h1
    _ = 2 ^ (a + (f - 1)) := (pow_add 2 a (f - 1)).symm
    _ ≤ 2 ^ (f * a) := Nat.pow_le_pow_right (by norm_num) h2
    _ = (2 ^ f) ^ a := pow_mul 2 f a

theorem two_mul_le_two_pow (f : ℕ) : 2 * f ≤ 2 ^ f := by
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · simp
  · simpa [mul_comm] using two_pow_mul_le_pow (a := 1) hf le_rfl

end CFSG.SeitzReduction.RankOne.LieTwo
