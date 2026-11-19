module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.ClassS
public import CFSG.GH74.Orders.LieType

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open CFSG.Blueprint

private lemma ordA_one_eq (q : ℕ) :
    CFSG.Open.ordA 1 q = q * (q ^ 2 - 1) / Nat.gcd 2 (q - 1) := by
  norm_num [CFSG.Open.ordA, Finset.Icc_self]

theorem eight_le_of_lieModel_psl_two_three {X : Type} [Group X] {e : ℕ}
    (h : LieModel X .PSL 2 3 e) (hb : classSBound ≤ Nat.card X) : 8 ≤ e := by
  by_contra hle
  push Not at hle
  have hcard : Nat.card X = CFSG.Open.ordA 1 (3 ^ e) := by
    simpa using CFSG.GH74.card_of_lieModel_PSL (G := X) (n := 2) (p := 3) (f := e)
      (by norm_num) h
  rw [hcard, ordA_one_eq] at hb
  interval_cases e <;> norm_num [classSBound] at hb

theorem thirtyTwo_dvd_card_of_lieModel_psl_two_three {X : Type} [Group X] {e : ℕ}
    (h : LieModel X .PSL 2 3 e) (he : 8 ∣ e) : 32 ∣ Nat.card X := by
  have hcard : Nat.card X = CFSG.Open.ordA 1 (3 ^ e) := by
    simpa using CFSG.GH74.card_of_lieModel_PSL (G := X) (n := 2) (p := 3) (f := e)
      (by norm_num) h
  obtain ⟨m, rfl⟩ := he
  rw [hcard, ordA_one_eq]
  have hodd : Odd (3 ^ (8 * m)) := (by norm_num : Odd 3).pow
  have hg : Nat.gcd 2 (3 ^ (8 * m) - 1) = 2 :=
    Nat.gcd_eq_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd odd_one))
  have h64 : 64 ∣ (3 ^ (8 * m)) ^ 2 - 1 := by
    have hpow : (3 ^ (8 * m)) ^ 2 = (3 ^ 16) ^ m := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      omega
    rw [hpow]
    have hbase : (64 : ℕ) ∣ 3 ^ 16 - 1 := by norm_num
    have hstep : 3 ^ 16 - 1 ∣ (3 ^ 16) ^ m - 1 :=
      Nat.sub_one_dvd_pow_sub_one (3 ^ 16) m
    exact dvd_trans hbase hstep
  obtain ⟨k, hk⟩ := h64
  refine ⟨3 ^ (8 * m) * k, ?_⟩
  rw [hg, hk, show 3 ^ (8 * m) * (64 * k) = 2 * (32 * (3 ^ (8 * m) * k)) by ring,
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

end CFSG.OddStandard.SmallF3.HypA2
