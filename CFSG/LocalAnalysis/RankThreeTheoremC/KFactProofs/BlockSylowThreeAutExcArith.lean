module

public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open

theorem dvd_toNat_pow_sub_neg_one_pow_of_dvd_succ {q d : ℕ} (hd : d ∣ q + 1) (i : ℕ) :
    d ∣ ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat := by
  have h : (d : ℤ) ∣ (q : ℤ) ^ i - (-1 : ℤ) ^ i := by
    have h1 := sub_dvd_pow_sub_pow (q : ℤ) (-1 : ℤ) i
    rw [sub_neg_eq_add] at h1
    exact (Int.natCast_dvd_natCast.2 hd).trans (by exact_mod_cast h1)
  rcases le_or_gt 0 ((q : ℤ) ^ i - (-1 : ℤ) ^ i) with h0 | h0
  · rw [← Int.toNat_of_nonneg h0] at h
    exact Int.natCast_dvd_natCast.1 h
  · rw [Int.toNat_of_nonpos h0.le]
    exact dvd_zero d

theorem three_pow_dvd_prod_twistedA_two {n : ℕ} (hn : 3 ≤ n) :
    3 ^ n ∣ ∏ i ∈ Finset.Icc 2 n, (((2 ^ 1 : ℕ) : ℤ) ^ i - (-1 : ℤ) ^ i).toNat := by
  have h3mem : 3 ∈ Finset.Icc 2 n := Finset.mem_Icc.2 ⟨by norm_num, hn⟩
  rw [← Finset.mul_prod_erase _ _ h3mem]
  have h9 : (((2 ^ 1 : ℕ) : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat = 3 ^ 2 := by norm_num
  have hcard : ((Finset.Icc 2 n).erase 3).card = n - 2 := by
    rw [Finset.card_erase_of_mem h3mem, Nat.card_Icc]
    omega
  have hrest : 3 ^ (n - 2) ∣
      ∏ i ∈ (Finset.Icc 2 n).erase 3, (((2 ^ 1 : ℕ) : ℤ) ^ i - (-1 : ℤ) ^ i).toNat := by
    rw [← hcard, ← Finset.prod_const]
    exact Finset.prod_dvd_prod_of_dvd _ _ fun i _ =>
      dvd_toNat_pow_sub_neg_one_pow_of_dvd_succ (by norm_num) i
  rw [h9, show 3 ^ n = 3 ^ 2 * 3 ^ (n - 2) by rw [← pow_add]; congr 1; omega]
  exact mul_dvd_mul_left _ hrest

theorem three_pow_dvd_ordTwistedA_odd {n : ℕ} (hn5 : 5 ≤ n) (hn : ¬Even n) :
    3 ^ (n / 2 + 3) ∣ ordTwistedA (n - 1) (2 ^ 1) := by
  unfold ordTwistedA
  rw [show n - 1 + 1 = n by omega]
  apply Nat.dvd_div_of_mul_dvd
  refine Dvd.dvd.mul_left (dvd_trans ?_ (three_pow_dvd_prod_twistedA_two (by omega))) _
  by_cases h3 : 3 ∣ n
  · rw [Nat.gcd_eq_right (by simpa using h3),
      show (2 ^ 1 + 1) * 3 ^ (n / 2 + 3) = 3 ^ (n / 2 + 4) by ring]
    refine Nat.pow_dvd_pow 3 ?_
    obtain ⟨m, rfl⟩ := h3
    rcases Nat.even_or_odd m with hm | ⟨j, rfl⟩
    · exact absurd (hm.mul_left 3) hn
    · omega
  · have hg : Nat.gcd n (2 ^ 1 + 1) = 1 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)
    rw [hg, one_mul]
    exact Nat.pow_dvd_pow 3 (by omega)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
