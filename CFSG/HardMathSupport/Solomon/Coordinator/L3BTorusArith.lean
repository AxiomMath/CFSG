module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

theorem three_pow_mod_eight (k : ℕ) :
    (k % 2 = 0 → 3 ^ k % 8 = 1) ∧ (k % 2 = 1 → 3 ^ k % 8 = 3) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · have := ih.1 h
      constructor <;> intro h' <;> omega
    · have := ih.2 h
      constructor <;> intro h' <;> omega

theorem prime_pow_eq_four {p n k : ℕ} (hp : p.Prime) (h : p ^ n = 3 ^ k + 1)
    (hmod : p ^ n % 3 = 1) : p ^ n = 4 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : p ^ n = 2 := by simpa using h
    omega
  have hodd : 3 ^ k % 2 = 1 := by
    rw [Nat.pow_mod]
    simp
  have h2 : 2 ∣ p ^ n := by omega
  have hn : n ≠ 0 := by
    rintro rfl
    have : 0 < 3 ^ k := by positivity
    rw [pow_zero] at h
    omega
  have hp2 : p = 2 :=
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  subst hp2
  by_cases hn3 : 3 ≤ n
  · exfalso
    have h8 : 8 ∣ 2 ^ n := by
      have : 2 ^ 3 ∣ 2 ^ n := pow_dvd_pow 2 hn3
      simpa using this
    have := three_pow_mod_eight k
    rcases Nat.mod_two_eq_zero_or_one k with hk2 | hk2
    · have := this.1 hk2
      omega
    · have := this.2 hk2
      omega
  · interval_cases n
    · exact absurd rfl hn
    · norm_num at hmod
    · norm_num

theorem prime_pow_succ_eq {p f k : ℕ} (hp : p.Prime) (h : p ^ f + 1 = 3 ^ k)
    (hmod : p ^ f % 3 = 2) : p ^ f = 2 ∨ p ^ f = 8 := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hmod
  have hodd3 : ∀ j : ℕ, 3 ^ j % 2 = 1 := fun j => by
    rw [Nat.pow_mod]
    simp
  have hk : k ≠ 0 := by
    rintro rfl
    have : 0 < p ^ f := pow_pos hp.pos f
    rw [pow_zero] at h
    omega
  have h2 : 2 ∣ p ^ f := by have := hodd3 k; omega
  have hp2 : p = 2 :=
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  subst hp2
  by_cases hf3 : 3 ≤ f
  · right
    have h8 : 8 ∣ 2 ^ f := by
      have : 2 ^ 3 ∣ 2 ^ f := pow_dvd_pow 2 hf3
      simpa using this
    have hkev : k % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one k with hk2 | hk2
      · exact hk2
      · have := (three_pow_mod_eight k).2 hk2
        omega
    obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
    obtain ⟨m, hm⟩ : ∃ m, m = 3 ^ j := ⟨_, rfl⟩
    have hm1 : 1 ≤ m := by rw [hm]; exact Nat.one_le_pow _ _ (by norm_num)
    have hmm : m * m = 2 ^ f + 1 := by rw [hm, ← pow_add, ← two_mul]; exact h.symm
    have hprod : (m - 1) * (m + 1) = 2 ^ f := by
      obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [hm'] at hmm ⊢
      simp only [Nat.add_sub_cancel]
      nlinarith
    have hd1 : m - 1 ∣ 2 ^ f := Dvd.intro _ hprod
    have hd2 : m + 1 ∣ 2 ^ f := Dvd.intro_left _ hprod
    obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd1
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd2
    have hmo : m % 2 = 1 := by rw [hm]; exact hodd3 j
    have hb' : 2 ^ b = 2 ^ a + 2 := by omega
    rcases Nat.lt_or_ge a 2 with ha2 | ha2
    · interval_cases a
      · omega
      · have hm3 : m = 3 := by omega
        subst hm3
        have : 2 ^ f = 8 := by nlinarith
        exact this
    · exfalso
      have h4a : 4 ∣ 2 ^ a := by
        have : 2 ^ 2 ∣ 2 ^ a := pow_dvd_pow 2 ha2
        simpa using this
      have hpa : 0 < 2 ^ a := by positivity
      rcases Nat.lt_or_ge b 2 with hb2 | hb2
      · interval_cases b <;> omega
      · have h4b : 4 ∣ 2 ^ b := by
          have : 2 ^ 2 ∣ 2 ^ b := pow_dvd_pow 2 hb2
          simpa using this
        omega
  · left
    interval_cases f
    · exact absurd rfl hf
    · rfl
    · simp at hmod

theorem exists_prime_ne_three_dvd_pred {p n : ℕ} (hp : p.Prime) (hmod : p ^ n % 3 = 1)
    (h4 : p ^ n ≠ 4) : ∃ r : ℕ, r.Prime ∧ r ≠ 3 ∧ r ∣ p ^ n - 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨2, Nat.prime_two, by norm_num, by simp⟩
  by_contra hcon
  push Not at hcon
  have hpos : p ^ n - 1 ≠ 0 := by
    have : 1 < p ^ n := Nat.one_lt_pow hn.ne' hp.one_lt
    omega
  have hpw := Nat.eq_prime_pow_of_unique_prime_dvd hpos
    (p := 3) (fun {d} hd hdd => by by_contra hne; exact hcon d hd hne hdd)
  have hq : p ^ n = 3 ^ (p ^ n - 1).primeFactorsList.length + 1 := by
    have : 1 ≤ p ^ n := Nat.one_le_pow _ _ hp.pos
    rw [← hpw]
    omega
  exact h4 (prime_pow_eq_four hp hq hmod)

theorem exists_prime_ne_three_dvd_succ {p f : ℕ} (hp : p.Prime) (hmod : p ^ f % 3 = 2)
    (h2 : p ^ f ≠ 2) (h8 : p ^ f ≠ 8) : ∃ r : ℕ, r.Prime ∧ r ≠ 3 ∧ r ∣ p ^ f + 1 := by
  by_contra hcon
  push Not at hcon
  have hpw := Nat.eq_prime_pow_of_unique_prime_dvd (by omega : p ^ f + 1 ≠ 0)
    (p := 3) (fun {d} hd hdd => by by_contra hne; exact hcon d hd hne hdd)
  rcases prime_pow_succ_eq hp hpw hmod with h | h
  · exact h2 h
  · exact h8 h

theorem exists_unit_ne_one_coprime_three (K : Type*) [Field K] [Finite K]
    (h3 : Nat.card K % 3 = 1) (h4 : Nat.card K ≠ 4) :
    ∃ a : Kˣ, a ≠ 1 ∧ ∃ n, Nat.Coprime 3 n ∧ a ^ n = 1 := by
  have := Fintype.ofFinite K
  obtain ⟨p, hp⟩ : ∃ p, CharP K p := CharP.exists K
  have hpp : p.Prime := CharP.char_is_prime K p
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨n, -, hn⟩ := FiniteField.card K p
  rw [← Nat.card_eq_fintype_card] at hn
  rw [hn] at h3 h4
  obtain ⟨r, hr, hr3, hrd⟩ := exists_prime_ne_three_dvd_pred hpp h3 h4
  have : Fact r.Prime := ⟨hr⟩
  have hcard : r ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hn]
    exact hrd
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' r hcard
  refine ⟨a, fun h => ?_, r, (Nat.coprime_primes Nat.prime_three hr).2 (Ne.symm hr3), ?_⟩
  · rw [h, orderOf_one] at ha
    exact hr.one_lt.ne ha
  · rw [← ha]
    exact pow_orderOf_eq_one a

theorem not_dvd_index_gl (q idx : ℕ) (hq : q % 3 = 1) (hq1 : 1 < q)
    (h : idx * (6 * (q - 1) ^ 3) = ∏ i : Fin 3, (q ^ 3 - q ^ (i : ℕ))) : ¬ 3 ∣ idx := by
  obtain ⟨k, rfl⟩ : ∃ k, q = 3 * k + 1 := ⟨q / 3, by omega⟩
  have hk : 1 ≤ k := by omega
  rintro ⟨t, rfl⟩
  rw [Fin.prod_univ_three] at h
  have e1 : (3 * k + 1) ^ 3 - (3 * k + 1) ^ (↑(0 : Fin 3) : ℕ) = 3 * k * (9 * k ^ 2 + 9 * k + 3) :=
    Nat.sub_eq_of_eq_add (by simp; ring)
  have e2 : (3 * k + 1) ^ 3 - (3 * k + 1) ^ (↑(1 : Fin 3) : ℕ) =
      (3 * k + 1) * (3 * k * (3 * k + 2)) := Nat.sub_eq_of_eq_add (by simp; ring)
  have e3 : (3 * k + 1) ^ 3 - (3 * k + 1) ^ (↑(2 : Fin 3) : ℕ) = (3 * k + 1) ^ 2 * (3 * k) :=
    Nat.sub_eq_of_eq_add (by simp; ring)
  rw [e1, e2, e3, show 3 * k + 1 - 1 = 3 * k by omega] at h
  have hpos : 0 < 3 * (3 * k) ^ 3 := by positivity
  have h6 : 6 * t = (3 * k + 1) ^ 3 * (3 * k + 2) * (3 * k ^ 2 + 3 * k + 1) := by
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    nlinarith [h]
  have h3 : 3 ∣ (3 * k + 1) ^ 3 * (3 * k + 2) * (3 * k ^ 2 + 3 * k + 1) := ⟨2 * t, by omega⟩
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h4 | h4
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h4 with h5 | h5
    · have := Nat.prime_three.dvd_of_dvd_pow h5
      omega
    · omega
  · omega

theorem not_dvd_index_gu (q idx : ℕ) (hq : q % 3 = 2) (hq1 : 1 < q)
    (h : idx * (6 * (q + 1) ^ 3) = q ^ 3 * (q + 1) * (q ^ 2 - 1) * (q ^ 3 + 1)) : ¬ 3 ∣ idx := by
  obtain ⟨k, rfl⟩ : ∃ k, q = 3 * k + 2 := ⟨q / 3, by omega⟩
  rintro ⟨t, rfl⟩
  have e1 : (3 * k + 2) ^ 2 - 1 = (3 * k + 1) * (3 * k + 3) :=
    Nat.sub_eq_of_eq_add (by ring)
  rw [e1] at h
  have hpos : 0 < 3 * (3 * k + 3) ^ 3 := by positivity
  have h6 : 6 * t = (3 * k + 2) ^ 3 * (3 * k + 1) * (3 * k ^ 2 + 3 * k + 1) := by
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    nlinarith [h]
  have h3 : 3 ∣ (3 * k + 2) ^ 3 * (3 * k + 1) * (3 * k ^ 2 + 3 * k + 1) := ⟨2 * t, by omega⟩
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h4 | h4
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h4 with h5 | h5
    · have := Nat.prime_three.dvd_of_dvd_pow h5
      omega
    · omega
  · omega

end CFSG.HardMathSupport.Solomon.Coordinator
