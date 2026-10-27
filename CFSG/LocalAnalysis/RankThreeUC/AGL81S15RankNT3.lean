module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankArith

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

theorem two_pow_add_one_eq_five_pow_aux1 (k : ℕ) : 5 ^ k % 24 = 1 ∨ 5 ^ k % 24 = 5 := by
  induction k with
  | zero => left; norm_num
  | succ j ih => rw [pow_succ]; omega

theorem two_pow_add_one_eq_five_pow_aux2 (n : ℕ) (hn : 3 ≤ n) :
    2 ^ n % 24 = 8 ∨ 2 ^ n % 24 = 16 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ j _ ih => rw [pow_succ]; omega

theorem two_pow_add_one_eq_five_pow {n k : ℕ} (hn : 1 ≤ n) (h : 2 ^ n + 1 = 5 ^ k) : n = 2 := by
  by_contra hne
  have hk := two_pow_add_one_eq_five_pow_aux1 k
  rw [← h] at hk
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · interval_cases n
    · norm_num at hk
    · exact hne rfl
  · have h2 := two_pow_add_one_eq_five_pow_aux2 n h3
    omega

theorem exists_prime_rank_ge_four_aux1 {n : ℕ} (hn : 2 ≤ n) :
    (if Even n then 2 ^ n + 1 else 2 ^ n - 1) ≠ 1 := by
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  split_ifs <;> omega

theorem exists_prime_rank_ge_four_aux2 {m z q : ℕ} (hm : 5 ≤ m) (hq : q.Prime)
    (hgood : q ∣ z ∨ q ≠ 5 ∨ 6 ≤ m) {P : Prop} [Decidable P] (hP : P → ¬ q ∣ z ∧ q ∣ m) :
    4 ≤ m - 1 - (if P then 1 else 0) := by
  by_cases hp : P
  · rw [if_pos hp]
    obtain ⟨hz, hqm⟩ := hP hp
    rcases hgood with h | h | h
    · exact absurd h hz
    · have hm6 : 6 ≤ m := by
        rcases Nat.lt_or_ge m 6 with hlt | hge
        · have hm5 : m = 5 := by omega
          rw [hm5] at hqm
          rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_five q hqm with h1 | h1
          · exact absurd h1 hq.one_lt.ne'
          · exact absurd h1 h
        · exact hge
      omega
    · omega
  · rw [if_neg hp]
    omega

theorem exists_prime_rank_ge_four_aux3 {n m z q : ℕ} (hm : 5 ≤ m) (hq : q.Prime)
    (hqN : q ∣ (if Even n then 2 ^ n + 1 else 2 ^ n - 1))
    (hgood : q ∣ z ∨ q ≠ 5 ∨ 6 ≤ m) :
    4 ≤ rkLin m (decide (Odd n)) (2 ^ n) q z := by
  have hQ : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hE : (if decide (Odd n) = true then eP (2 ^ n) q else eM (2 ^ n) q) = 1 := by
    rcases Nat.even_or_odd n with hev | hodd
    · rw [if_pos hev] at hqN
      have hnodd : ¬ Odd n := Nat.not_odd_iff_even.mpr hev
      simp only [decide_eq_true_eq]
      rw [if_neg hnodd]
      exact eM_eq_one_iff.mpr hqN
    · have hnev : ¬ Even n := Nat.not_even_iff_odd.mpr hodd
      rw [if_neg hnev] at hqN
      simp only [decide_eq_true_eq]
      rw [if_pos hodd]
      exact (eP_eq_one_iff hQ).mpr hqN
  unfold rkLin
  rw [if_pos hE]
  apply exists_prime_rank_ge_four_aux2 hm hq hgood
  exact fun hP => ⟨hP.1, hP.2.1⟩

theorem exists_prime_rank_ge_four_aux4 (t : ℕ) :
    2 ^ (2 * t + 1) % 5 = 2 ∨ 2 ^ (2 * t + 1) % 5 = 3 := by
  have h4 : 4 ^ t % 5 = 1 ∨ 4 ^ t % 5 = 4 := by
    induction t with
    | zero => left; norm_num
    | succ j ih => rw [pow_succ]; omega
  have he : 2 ^ (2 * t + 1) = 2 * 4 ^ t := by
    rw [pow_succ, pow_mul]; ring
  rw [he]
  omega

theorem exists_prime_rank_ge_four (n m z : ℕ) (hn : 2 ≤ n) (hm5 : 5 ≤ m) (hm7 : m ≤ 7) :
    (m = 5 ∧ n = 2 ∧ ¬ 5 ∣ z) ∨
      ∃ q : ℕ, q.Prime ∧ q ∣ (if Even n then 2 ^ n + 1 else 2 ^ n - 1) ∧
        4 ≤ rkLin m (decide (Odd n)) (2 ^ n) q z := by
  obtain ⟨q, hq, hqN⟩ := Nat.exists_prime_and_dvd (exists_prime_rank_ge_four_aux1 hn)
  by_cases hm6 : 6 ≤ m
  · exact Or.inr ⟨q, hq, hqN, exists_prime_rank_ge_four_aux3 hm5 hq hqN (Or.inr (Or.inr hm6))⟩
  by_cases hA : ∃ q' : ℕ, q'.Prime ∧ q' ∣ (if Even n then 2 ^ n + 1 else 2 ^ n - 1) ∧ q' ≠ 5
  · obtain ⟨q', hq', hq'N, hq'5⟩ := hA
    exact Or.inr ⟨q', hq', hq'N, exists_prime_rank_ge_four_aux3 hm5 hq' hq'N (Or.inr (Or.inl hq'5))⟩
  have hm : m = 5 := by omega
  subst hm
  have hq5 : q = 5 := by
    by_contra hne
    exact hA ⟨q, hq, hqN, hne⟩
  subst hq5
  by_cases hz : 5 ∣ z
  · exact Or.inr ⟨5, hq, hqN, exists_prime_rank_ge_four_aux3 hm5 hq hqN (Or.inl hz)⟩
  refine Or.inl ⟨rfl, ?_, hz⟩
  by_cases hev : Even n
  · rw [if_pos hev] at hA
    have hall : ∀ {d : ℕ}, d.Prime → d ∣ 2 ^ n + 1 → d = 5 := by
      intro d hd hdv
      by_contra hne
      exact hA ⟨d, hd, hdv, hne⟩
    have hN := Nat.eq_prime_pow_of_unique_prime_dvd (n := 2 ^ n + 1) (p := 5) (by positivity)
      hall
    exact two_pow_add_one_eq_five_pow (by omega) hN
  · exfalso
    rw [if_neg hev] at hqN
    obtain ⟨t, rfl⟩ := Nat.not_even_iff_odd.mp hev
    have h1 := exists_prime_rank_ge_four_aux4 t
    have h2 : 1 ≤ 2 ^ (2 * t + 1) := Nat.one_le_two_pow
    generalize 2 ^ (2 * t + 1) = x at hqN h1 h2
    omega

end CFSG.LocalAnalysis.RankThreeUC.S15
