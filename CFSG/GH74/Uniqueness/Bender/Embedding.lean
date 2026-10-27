module

public import CFSG.GH74.Uniqueness.Bender.Models

public section

namespace CFSG.GH74.Uniqueness.Bender

theorem sz_mod (a : ℕ) :
    2 ^ (2 * a + 1) % 3 = 2 ∧ (2 ^ (2 * a + 1)) ^ 2 % 5 = 4 ∧
      (2 ^ (2 * a + 1) % 5 = 2 ∨ 2 ^ (2 * a + 1) % 5 = 3) := by
  have h4 : 2 ^ (2 * a + 1) = 4 ^ a * 2 := by
    rw [pow_succ, pow_mul]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [h4, Nat.mul_mod, Nat.pow_mod]
    norm_num
  · have : (2 ^ (2 * a + 1)) ^ 2 = 16 ^ a * 4 := by
      rw [← pow_mul, show (2 * a + 1) * 2 = 4 * a + 2 by ring, pow_add, pow_mul]
      norm_num
    rw [this, Nat.mul_mod, Nat.pow_mod]
    norm_num
  · rcases Nat.even_or_odd' a with ⟨k, rfl | rfl⟩
    · left
      have : 2 ^ (2 * (2 * k) + 1) = 16 ^ k * 2 := by
        rw [show 2 * (2 * k) + 1 = 4 * k + 1 by ring, pow_add, pow_mul]
        norm_num
      rw [this, Nat.mul_mod, Nat.pow_mod]
      norm_num
    · right
      have : 2 ^ (2 * (2 * k + 1) + 1) = 16 ^ k * 8 := by
        rw [show 2 * (2 * k + 1) + 1 = 4 * k + 3 by ring, pow_add, pow_mul]
        norm_num
      rw [this, Nat.mul_mod, Nat.pow_mod]
      norm_num

theorem not_dvd_lin_sz (a : ℕ) :
    ¬ (((2 ^ (2 * a + 1)) ^ 1 + 1) * ((2 ^ (2 * a + 1)) ^ 1 * ((2 ^ (2 * a + 1) - 1) * 1)) ∣
      ((2 ^ (2 * a + 1)) ^ 2 + 1) * ((2 ^ (2 * a + 1)) ^ 2 * ((2 ^ (2 * a + 1) - 1) * 1))) := by
  intro h
  obtain ⟨h3, h5, h5'⟩ := sz_mod a
  generalize 2 ^ (2 * a + 1) = q at *
  have hq1 : 1 ≤ q := by omega
  have h31 : 3 ∣ ((q ^ 1 + 1) * (q ^ 1 * ((q - 1) * 1))) :=
    Dvd.dvd.mul_right (by rw [pow_one]; omega) _
  have h3sq : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h3]
  have hnot : ¬ 3 ∣ ((q ^ 2 + 1) * (q ^ 2 * ((q - 1) * 1))) := by
    intro hd
    rw [Nat.Prime.dvd_mul Nat.prime_three, Nat.Prime.dvd_mul Nat.prime_three,
      Nat.Prime.dvd_mul Nat.prime_three] at hd
    omega
  exact hnot (h31.trans h)

theorem lt_lin_sz (q : ℕ) (hq : 8 ≤ q) :
    (q ^ 1 + 1) * (q ^ 1 * ((q - 1) * 1)) < (q ^ 2 + 1) * (q ^ 2 * ((q - 1) * 1)) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 8 := ⟨q - 8, by omega⟩
  have : r + 8 - 1 = r + 7 := by omega
  rw [this]
  nlinarith [Nat.zero_le r, Nat.zero_le (r * r), Nat.zero_le (r * r * r),
    Nat.zero_le (r * r * r * r)]

theorem lt_lin_uni (q e : ℕ) (hq : 4 ≤ q) (he : 1 ≤ e) :
    (q ^ 1 + 1) * (q ^ 1 * ((q - 1) * 1)) < (q ^ 3 + 1) * (q ^ 3 * ((q - 1) * e)) := by
  have h1 : q ^ 1 + 1 < q ^ 3 + 1 := by
    have : q ^ 1 < q ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  have h2 : q ^ 1 * ((q - 1) * 1) ≤ q ^ 3 * ((q - 1) * e) :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) (by norm_num)) (Nat.mul_le_mul_left _ he)
  have hpos : 0 < q ^ 3 * ((q - 1) * e) :=
    Nat.mul_pos (by positivity) (Nat.mul_pos (by omega) (by omega))
  exact Nat.mul_lt_mul_of_lt_of_le h1 h2 hpos

theorem lt_sz_uni (q e : ℕ) (hq : 8 ≤ q) (he : 1 ≤ e) :
    (q ^ 2 + 1) * (q ^ 2 * ((q - 1) * 1)) < (q ^ 3 + 1) * (q ^ 3 * ((q - 1) * e)) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 8 := ⟨q - 8, by omega⟩
  have h1 : r + 8 - 1 = r + 7 := by omega
  rw [h1]
  obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
  nlinarith [Nat.zero_le r, Nat.zero_le (r * r), Nat.zero_le (r * r * r), Nat.zero_le f,
    Nat.zero_le (r * f), Nat.zero_le (r * r * f), Nat.zero_le (r * r * r * f),
    Nat.zero_le (r * r * r * r), Nat.zero_le (r * r * r * r * r)]

theorem five_not_dvd_uni (q : ℕ) (h5 : q % 5 = 2 ∨ q % 5 = 3) (e : ℕ) (he : e ∣ q + 1) :
    ¬ 5 ∣ (q ^ 3 + 1) * (q ^ 3 * ((q - 1) * e)) := by
  intro hd
  have h5p : Nat.Prime 5 := by norm_num
  have hne : ¬ 5 ∣ e := fun h => by
    have := h.trans he
    omega
  have h53 : q ^ 3 % 5 = 3 ∨ q ^ 3 % 5 = 2 := by
    rcases h5 with h | h <;> simp [Nat.pow_mod, h]
  have hq0 : ¬ 5 ∣ q ^ 3 := by
    intro h
    omega
  have hq1 : q ≥ 1 := by omega
  rw [Nat.Prime.dvd_mul h5p, Nat.Prime.dvd_mul h5p, Nat.Prime.dvd_mul h5p] at hd
  omega

theorem unitary_e_pos (n : ℕ) : 1 ≤ (2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1) :=
  Nat.div_pos (Nat.gcd_le_right _ (Nat.succ_pos _)) (Nat.gcd_pos_of_pos_left _ (by norm_num))

theorem unitary_e_dvd (n : ℕ) : (2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1) ∣ 2 ^ n + 1 :=
  Nat.div_dvd_of_dvd (Nat.gcd_dvd_right 3 (2 ^ n + 1))

theorem three_dvd_linear_card (m : ℕ) :
    3 ∣ ((2 ^ m) ^ 1 + 1) * ((2 ^ m) ^ 1 * ((2 ^ m - 1) * 1)) := by
  have hmod : 2 ^ m % 3 = 1 ∨ 2 ^ m % 3 = 2 := by
    have : ¬ 3 ∣ 2 ^ m := fun hd => by
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
      omega
    omega
  rcases hmod with hm | hm
  · have hd : 3 ∣ 2 ^ m - 1 := by omega
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_right hd 1) _) _
  · have hd : 3 ∣ 2 ^ m + 1 := by omega
    exact Dvd.dvd.mul_right (by rwa [pow_one]) _

theorem not_three_dvd_sz_card (a : ℕ) :
    ¬ 3 ∣ ((2 ^ (2 * a + 1)) ^ 2 + 1) * ((2 ^ (2 * a + 1)) ^ 2 * ((2 ^ (2 * a + 1) - 1) * 1)) := by
  intro hd
  obtain ⟨h3, -, -⟩ := sz_mod a
  generalize 2 ^ (2 * a + 1) = q at *
  have hq1 : 1 ≤ q := by omega
  rw [Nat.Prime.dvd_mul Nat.prime_three, Nat.Prime.dvd_mul Nat.prime_three,
    Nat.Prime.dvd_mul Nat.prime_three] at hd
  have h3sq : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h3]
  omega

theorem BenderType.embedding_index
    {K K' : Type*} [Group K] [Group K'] [Finite K] [Finite K']
    {n i e i' e' : ℕ} (h : BenderType K n i e) (h' : BenderType K' n i' e') (f : K →* K')
    (hf : Function.Injective f) : i = i' ∨ (i = 1 ∧ i' = 3) := by
  have hd : Nat.card K ∣ Nat.card K' := Subgroup.card_dvd_of_injective f hf
  rw [h.card_eq, h'.card_eq] at hd
  rcases h.cases' with ⟨rfl, rfl, hn⟩ | ⟨rfl, rfl, a, ha, rfl⟩ | ⟨rfl, rfl, hn⟩
  · rcases h'.cases' with ⟨rfl, rfl, hn'⟩ | ⟨rfl, rfl, a', ha', hn'⟩ | ⟨rfl, rfl, hn'⟩
    · exact Or.inl rfl
    · subst hn'
      exact absurd hd (not_dvd_lin_sz a')
    · exact Or.inr ⟨rfl, rfl⟩
  · have hq8 : 8 ≤ 2 ^ (2 * a + 1) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rcases h'.cases' with ⟨rfl, rfl, hn'⟩ | ⟨rfl, rfl, a', ha', hn'⟩ | ⟨rfl, rfl, hn'⟩
    · exfalso
      have hpos : 0 < (((2 ^ (2 * a + 1)) ^ 1 + 1) * ((2 ^ (2 * a + 1)) ^ 1 *
          ((2 ^ (2 * a + 1) - 1) * 1))) :=
        Nat.mul_pos (by positivity) (Nat.mul_pos (by positivity) (Nat.mul_pos (by omega) (by omega)))
      exact absurd (Nat.le_of_dvd hpos hd) (not_le.mpr (lt_lin_sz _ hq8))
    · exact Or.inl rfl
    · exfalso
      obtain ⟨h3, h5, h5'⟩ := sz_mod a
      have hSz : 5 ∣ (((2 ^ (2 * a + 1)) ^ 2 + 1) * ((2 ^ (2 * a + 1)) ^ 2 *
          ((2 ^ (2 * a + 1) - 1) * 1))) := Dvd.dvd.mul_right (by omega) _
      exact five_not_dvd_uni _ h5' _ (unitary_e_dvd _) (hSz.trans hd)
  · rcases h'.cases' with ⟨rfl, rfl, hn'⟩ | ⟨rfl, rfl, a, ha, hn'⟩ | ⟨rfl, rfl, hn'⟩
    · exfalso
      have hq4 : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      have hpos : 0 < (((2 ^ n) ^ 1 + 1) * ((2 ^ n) ^ 1 * ((2 ^ n - 1) * 1))) :=
        Nat.mul_pos (by positivity) (Nat.mul_pos (by positivity) (Nat.mul_pos (by omega) (by omega)))
      exact absurd (Nat.le_of_dvd hpos hd) (not_le.mpr (lt_lin_uni _ _ hq4 (unitary_e_pos n)))
    · exfalso
      subst hn'
      have hq8 : 8 ≤ 2 ^ (2 * a + 1) := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hpos : 0 < (((2 ^ (2 * a + 1)) ^ 2 + 1) * ((2 ^ (2 * a + 1)) ^ 2 *
          ((2 ^ (2 * a + 1) - 1) * 1))) :=
        Nat.mul_pos (by positivity) (Nat.mul_pos (by positivity) (Nat.mul_pos (by omega) (by omega)))
      exact absurd (Nat.le_of_dvd hpos hd) (not_le.mpr (lt_sz_uni _ _ hq8 (unitary_e_pos _)))
    · exact Or.inl rfl

end CFSG.GH74.Uniqueness.Bender
