module

public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5Omega

open CFSG.Open

private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private theorem five_dvd_pow_sub_one_iff {q k : ℕ} (hq : 1 ≤ q) :
    5 ∣ q ^ k - 1 ↔ orderOf (q : ZMod 5) ∣ k := by
  rw [orderOf_dvd_iff_pow_eq_one, ← ZMod.natCast_eq_zero_iff,
    Nat.cast_sub (Nat.one_le_pow _ _ hq), sub_eq_zero]
  simp

private theorem orderOf_cases {q : ℕ} (hq : ¬ 5 ∣ q) :
    (q % 5 = 1 ∧ orderOf (q : ZMod 5) = 1) ∨ (q % 5 = 4 ∧ orderOf (q : ZMod 5) = 2) ∨
      ((q % 5 = 2 ∨ q % 5 = 3) ∧ orderOf (q : ZMod 5) = 4) := by
  have hcast : (q : ZMod 5) = ((q % 5 : ℕ) : ZMod 5) := (ZMod.natCast_mod q 5).symm
  have h : q % 5 = 1 ∨ q % 5 = 2 ∨ q % 5 = 3 ∨ q % 5 = 4 := by omega
  rw [hcast]
  rcases h with h | h | h | h <;> rw [h]
  · exact Or.inl ⟨rfl, by simp⟩
  · exact Or.inr (Or.inr ⟨Or.inl rfl, orderOf_eq_prime_pow (p := 2) (n := 1) (by decide)
      (by decide)⟩)
  · exact Or.inr (Or.inr ⟨Or.inr rfl, orderOf_eq_prime_pow (p := 2) (n := 1) (by decide)
      (by decide)⟩)
  · exact Or.inr (Or.inl ⟨rfl, orderOf_eq_prime (by decide) (by decide)⟩)

private theorem v5_of_not_dvd_25 {k : ℕ} (hk : k ≠ 0) (hk25 : ¬ 25 ∣ k) :
    padicValNat 5 k = if 5 ∣ k then 1 else 0 := by
  split_ifs with h
  · have h1 := one_le_padicValNat_of_dvd hk h
    have h2 : ¬ 2 ≤ padicValNat 5 k := fun h2 =>
      hk25 (by simpa using (padicValNat_dvd_iff_le (p := 5) (n := 2) hk).2 h2)
    omega
  · exact padicValNat.eq_zero_of_not_dvd h

private theorem v5_pow_sub_one {q e A k : ℕ} (hq : 2 ≤ q) (h5 : ¬ 5 ∣ q)
    (he : orderOf (q : ZMod 5) = e) (he4 : e ∣ 4) (hA : padicValNat 5 (q ^ e - 1) = A)
    (hk : k ≠ 0) (hk25 : ¬ 25 ∣ k) :
    padicValNat 5 (q ^ k - 1) = if e ∣ k then A + (if 5 ∣ k then 1 else 0) else 0 := by
  by_cases hek : e ∣ k
  · rw [if_pos hek]
    obtain ⟨j, rfl⟩ := hek
    have he0 : e ≠ 0 := by rintro rfl; simp at hk
    have hj : j ≠ 0 := by rintro rfl; simp at hk
    have hdvd : 5 ∣ q ^ e - 1 := (five_dvd_pow_sub_one_iff (by omega)).2 (he ▸ dvd_rfl)
    have h1 : 1 < q ^ e := Nat.one_lt_pow he0 (by omega)
    have hpq : ¬ 5 ∣ q ^ e := fun h => h5 (Nat.prime_five.dvd_of_dvd_pow h)
    have hlte := padicValNat.pow_sub_pow (p := 5) (by decide) (x := q ^ e) (y := 1) h1
      (by simpa using hdvd) hpq hj
    rw [one_pow, ← pow_mul] at hlte
    have he5 : ¬ 5 ∣ e := fun h => absurd (h.trans he4) (by decide)
    rw [hlte, hA, ← v5_of_not_dvd_25 hk hk25, padicValNat.mul he0 hj,
      padicValNat.eq_zero_of_not_dvd he5, zero_add]
  · rw [if_neg hek]
    exact padicValNat.eq_zero_of_not_dvd fun h =>
      hek (he ▸ (five_dvd_pow_sub_one_iff (by omega)).1 h)

private theorem exists_lte_data {q : ℕ} (hq2 : 2 ≤ q) (hq : ¬ 5 ∣ q) :
    ∃ e A, orderOf (q : ZMod 5) = e ∧
      ((q % 5 = 1 ∧ e = 1) ∨ (q % 5 = 4 ∧ e = 2) ∨ ((q % 5 = 2 ∨ q % 5 = 3) ∧ e = 4)) ∧
      1 ≤ A ∧ ∀ k, k ≠ 0 → ¬ 25 ∣ k →
        padicValNat 5 (q ^ k - 1) = if e ∣ k then A + (if 5 ∣ k then 1 else 0) else 0 := by
  have hc := orderOf_cases hq
  have he4 : orderOf (q : ZMod 5) ∣ 4 := by
    rcases hc with ⟨-, he⟩ | ⟨-, he⟩ | ⟨-, he⟩ <;> rw [he] <;> decide
  have he0 : orderOf (q : ZMod 5) ≠ 0 := by
    rcases hc with ⟨-, he⟩ | ⟨-, he⟩ | ⟨-, he⟩ <;> rw [he] <;> decide
  have h1 : 1 < q ^ orderOf (q : ZMod 5) := Nat.one_lt_pow he0 (by omega)
  exact ⟨_, _, rfl, hc, one_le_padicValNat_of_dvd (by omega)
    ((five_dvd_pow_sub_one_iff (by omega)).2 dvd_rfl), fun k hk hk25 =>
    v5_pow_sub_one hq2 hq rfl he4 rfl hk hk25⟩

private theorem v5_pow_add_one {q B k : ℕ} (h5 : ¬ 5 ∣ q) (hq4 : q % 5 = 4)
    (hB : padicValNat 5 (q + 1) = B) (hk : Odd k) (hk25 : ¬ 25 ∣ k) :
    padicValNat 5 (q ^ k + 1) = B + if 5 ∣ k then 1 else 0 := by
  have hlte := padicValNat.pow_add_pow (p := 5) (by decide) (x := q) (y := 1) (by omega) h5 hk
  rw [one_pow] at hlte
  rw [hlte, hB, v5_of_not_dvd_25 hk.pos.ne' hk25]

private theorem not_five_dvd_pow_add_one {q k : ℕ} (hq : q % 5 = 1 ∨ q % 5 = 2 ∨ q % 5 = 3)
    (hk : k = 5 ∨ k = 9) : ¬ 5 ∣ q ^ k + 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
    ← ZMod.natCast_mod q 5]
  rcases hq with h | h | h <;> rcases hk with rfl | rfl <;> rw [h] <;> decide

private theorem v5_div {N g : ℕ} (hg : g ∣ N) (hg5 : ¬ 5 ∣ g) :
    padicValNat 5 (N / g) = padicValNat 5 N := by
  rw [padicValNat.div_of_dvd hg, padicValNat.eq_zero_of_not_dvd hg5, Nat.sub_zero]

private theorem pow_sub_one_pos {q k : ℕ} (hq : 2 ≤ q) (hk : k ≠ 0) : 0 < q ^ k - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow hk (by omega))

theorem factorization_ordE6_ne_five {q : ℕ} (hq : ¬ 5 ∣ q) : (ordE6 q).factorization 5 ≠ 5 := by
  obtain rfl | hq2 : q = 1 ∨ 2 ≤ q := by omega
  · simp [ordE6]
  have hg : Nat.gcd 3 (q - 1) ∣ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) *
      (q ^ 6 - 1) * (q ^ 5 - 1) * (q ^ 2 - 1) :=
    (Nat.gcd_dvd_right _ _).trans ((Nat.sub_one_dvd_pow_sub_one q 2).trans (dvd_mul_left _ _))
  have hg5 : ¬ 5 ∣ Nat.gcd 3 (q - 1) := fun h =>
    absurd (h.trans (Nat.gcd_dvd_left _ _)) (by decide)
  rw [Nat.factorization_def _ Nat.prime_five, ordE6, v5_div hg hg5]
  have hq0 : 0 < q := by omega
  have h12 := pow_sub_one_pos hq2 (k := 12) (by norm_num)
  have h9 := pow_sub_one_pos hq2 (k := 9) (by norm_num)
  have h8 := pow_sub_one_pos hq2 (k := 8) (by norm_num)
  have h6 := pow_sub_one_pos hq2 (k := 6) (by norm_num)
  have h5 := pow_sub_one_pos hq2 (k := 5) (by norm_num)
  have h2 := pow_sub_one_pos hq2 (k := 2) (by norm_num)
  simp (disch := positivity) only [padicValNat.mul]
  rw [padicValNat.pow, padicValNat.eq_zero_of_not_dvd hq, mul_zero, zero_add]
  obtain ⟨e, A, -, he, hA, hv⟩ := exists_lte_data hq2 hq
  simp (disch := decide) only [hv]
  rcases he with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp only [Nat.reduceDvd, ↓reduceIte] <;>
    omega

theorem factorization_ordE7_ne_five {q : ℕ} (hq : ¬ 5 ∣ q) : (ordE7 q).factorization 5 ≠ 5 := by
  obtain rfl | hq2 : q = 1 ∨ 2 ≤ q := by omega
  · simp [ordE7]
  have hg : Nat.gcd 2 (q - 1) ∣ q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) *
      (q ^ 10 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1) :=
    (Nat.gcd_dvd_right _ _).trans ((Nat.sub_one_dvd_pow_sub_one q 2).trans (dvd_mul_left _ _))
  have hg5 : ¬ 5 ∣ Nat.gcd 2 (q - 1) := fun h =>
    absurd (h.trans (Nat.gcd_dvd_left _ _)) (by decide)
  rw [Nat.factorization_def _ Nat.prime_five, ordE7, v5_div hg hg5]
  have hq0 : 0 < q := by omega
  have h18 := pow_sub_one_pos hq2 (k := 18) (by norm_num)
  have h14 := pow_sub_one_pos hq2 (k := 14) (by norm_num)
  have h12 := pow_sub_one_pos hq2 (k := 12) (by norm_num)
  have h10 := pow_sub_one_pos hq2 (k := 10) (by norm_num)
  have h8 := pow_sub_one_pos hq2 (k := 8) (by norm_num)
  have h6 := pow_sub_one_pos hq2 (k := 6) (by norm_num)
  have h2 := pow_sub_one_pos hq2 (k := 2) (by norm_num)
  simp (disch := positivity) only [padicValNat.mul]
  rw [padicValNat.pow, padicValNat.eq_zero_of_not_dvd hq, mul_zero, zero_add]
  obtain ⟨e, A, -, he, hA, hv⟩ := exists_lte_data hq2 hq
  simp (disch := decide) only [hv]
  rcases he with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp only [Nat.reduceDvd, ↓reduceIte] <;>
    omega

theorem factorization_ordTwistedE6_ne_five {q : ℕ} (hq : ¬ 5 ∣ q) :
    (ordTwistedE6 q).factorization 5 ≠ 5 := by
  obtain rfl | hq2 : q = 1 ∨ 2 ≤ q := by omega
  · simp [ordTwistedE6]
  have hq5 : q + 1 ∣ q ^ 5 + 1 := by
    simpa using Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 5)
  have hg : Nat.gcd 3 (q + 1) ∣ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) *
      (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1) :=
    (Nat.gcd_dvd_right _ _).trans (hq5.trans ((dvd_mul_left _ _).mul_right _))
  have hg5 : ¬ 5 ∣ Nat.gcd 3 (q + 1) := fun h =>
    absurd (h.trans (Nat.gcd_dvd_left _ _)) (by decide)
  rw [Nat.factorization_def _ Nat.prime_five, ordTwistedE6, v5_div hg hg5]
  have hq0 : 0 < q := by omega
  have h12 := pow_sub_one_pos hq2 (k := 12) (by norm_num)
  have h8 := pow_sub_one_pos hq2 (k := 8) (by norm_num)
  have h6 := pow_sub_one_pos hq2 (k := 6) (by norm_num)
  have h2 := pow_sub_one_pos hq2 (k := 2) (by norm_num)
  simp (disch := positivity) only [padicValNat.mul]
  rw [padicValNat.pow, padicValNat.eq_zero_of_not_dvd hq, mul_zero, zero_add]
  obtain ⟨e, A, -, he, hA, hv⟩ := exists_lte_data hq2 hq
  simp (disch := decide) only [hv]
  rcases he with ⟨h1, rfl⟩ | ⟨h4, rfl⟩ | ⟨h23, rfl⟩
  · rw [padicValNat.eq_zero_of_not_dvd (not_five_dvd_pow_add_one (Or.inl h1) (Or.inr rfl)),
      padicValNat.eq_zero_of_not_dvd (not_five_dvd_pow_add_one (Or.inl h1) (Or.inl rfl))]
    simp only [Nat.reduceDvd, ↓reduceIte]
    omega
  · obtain ⟨B, hB⟩ : ∃ B, padicValNat 5 (q + 1) = B := ⟨_, rfl⟩
    have hB1 : 1 ≤ B := by
      rw [← hB]
      exact one_le_padicValNat_of_dvd (by omega) (by omega)
    rw [v5_pow_add_one (k := 9) hq h4 hB (by decide) (by decide),
      v5_pow_add_one (k := 5) hq h4 hB (by decide) (by decide)]
    simp only [Nat.reduceDvd, ↓reduceIte]
    omega
  · rw [padicValNat.eq_zero_of_not_dvd (not_five_dvd_pow_add_one (Or.inr h23) (Or.inr rfl)),
      padicValNat.eq_zero_of_not_dvd (not_five_dvd_pow_add_one (Or.inr h23) (Or.inl rfl))]
    simp only [Nat.reduceDvd, ↓reduceIte]
    omega

theorem orderOf_eq_four_of_factorization_ordE8 {q : ℕ} (hq : ¬ 5 ∣ q)
    (h : (ordE8 q).factorization 5 = 5) : orderOf ((q : ℕ) : ZMod 5) = 4 := by
  obtain rfl | hq2 : q = 1 ∨ 2 ≤ q := by omega
  · simp [ordE8] at h
  rw [Nat.factorization_def _ Nat.prime_five, ordE8] at h
  have hq0 : 0 < q := by omega
  have h30 := pow_sub_one_pos hq2 (k := 30) (by norm_num)
  have h24 := pow_sub_one_pos hq2 (k := 24) (by norm_num)
  have h20 := pow_sub_one_pos hq2 (k := 20) (by norm_num)
  have h18 := pow_sub_one_pos hq2 (k := 18) (by norm_num)
  have h14 := pow_sub_one_pos hq2 (k := 14) (by norm_num)
  have h12 := pow_sub_one_pos hq2 (k := 12) (by norm_num)
  have h8 := pow_sub_one_pos hq2 (k := 8) (by norm_num)
  have h2 := pow_sub_one_pos hq2 (k := 2) (by norm_num)
  simp (disch := positivity) only [padicValNat.mul] at h
  rw [padicValNat.pow, padicValNat.eq_zero_of_not_dvd hq, mul_zero, zero_add] at h
  obtain ⟨e, A, hord, he, hA, hv⟩ := exists_lte_data hq2 hq
  simp (disch := decide) only [hv] at h
  rcases he with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
  · simp only [Nat.reduceDvd, ↓reduceIte] at h
    omega
  · simp only [Nat.reduceDvd, ↓reduceIte] at h
    omega
  · exact hord

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5Omega
