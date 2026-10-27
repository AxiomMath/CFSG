module

public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels
public import CFSG.ClassicalInvolution.Orders.Symplectic
public import CFSG.RankThree.PartTwo.KFacts.K71OddCharArith
public import CFSG.Sporadic.Suz.Simple
public import CFSG.Sporadic.ON

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.Assembly.LowTwoRank

theorem card_eq_of_lieModel_psl_three {X : Type} [Group X] {n : ℕ}
    (hX : Blueprint.LieModel X .PSL 3 2 n) :
    Nat.card X = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) /
      Nat.gcd 3 (2 ^ n - 1) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
    LieType.Steinberg.CentralExt.GriessNative.classical_of_lieModel hX (by decide)
  rw [Nat.card_congr e.toEquiv, Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num),
    hK, show Finset.Icc 2 3 = {2, 3} by rfl, Finset.prod_pair (by norm_num)]

theorem padicValNat_card_of_lieModel_psl_three {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (hX : Blueprint.LieModel X .PSL 3 2 n) : padicValNat 2 (Nat.card X) = 3 * n := by
  rw [card_eq_of_lieModel_psl_three hX]
  set q := 2 ^ n with hq
  have hqe : Even q := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have h2 : Odd (q ^ 2 - 1) :=
    Nat.Even.sub_odd (Nat.one_le_pow _ _ hq1) (hqe.pow_of_ne_zero (by norm_num)) odd_one
  have h3 : Odd (q ^ 3 - 1) :=
    Nat.Even.sub_odd (Nat.one_le_pow _ _ hq1) (hqe.pow_of_ne_zero (by norm_num)) odd_one
  have hB : Odd ((q ^ 2 - 1) * (q ^ 3 - 1)) := h2.mul h3
  have hd : Nat.gcd 3 (q - 1) ∣ (q ^ 2 - 1) * (q ^ 3 - 1) := by
    have h1 : q ^ 1 - 1 ∣ q ^ 2 - 1 := Nat.pow_sub_one_dvd_pow_sub_one (x := q) (one_dvd 2)
    rw [pow_one] at h1
    exact (Nat.gcd_dvd_right 3 (q - 1)).trans (h1.mul_right _)
  obtain ⟨c, hc⟩ := hd
  have hcodd : Odd c := Nat.Odd.of_mul_right (hc ▸ hB)
  have hd0 : 0 < Nat.gcd 3 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  rw [hc, ← mul_assoc, mul_comm (q ^ 3), mul_assoc, Nat.mul_div_cancel_left _ hd0,
    padicValNat.mul (by positivity) hcodd.pos.ne', hq, ← pow_mul,
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hcodd.not_two_dvd_nat]
  ring

theorem card_lt_of_lieModel_psl_three {X : Type} [Group X] {n : ℕ}
    (hX : Blueprint.LieModel X .PSL 3 2 n) : Nat.card X < 2 ^ (8 * n) := by
  rw [card_eq_of_lieModel_psl_three hX]
  set q := 2 ^ n with hq
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have h2 : q ^ 2 - 1 < q ^ 2 := by have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1; omega
  have h3 : q ^ 3 - 1 < q ^ 3 := by have : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq1; omega
  calc q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1)
        ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := Nat.div_le_self _ _
    _ < q ^ 3 * (q ^ 2 * q ^ 3) := by
        apply Nat.mul_lt_mul_of_pos_left _ (by positivity)
        calc (q ^ 2 - 1) * (q ^ 3 - 1) ≤ (q ^ 2 - 1) * q ^ 3 := Nat.mul_le_mul_left _ h3.le
          _ < q ^ 2 * q ^ 3 := Nat.mul_lt_mul_of_pos_right h2 (by positivity)
    _ = 2 ^ (8 * n) := by rw [hq]; ring

theorem two_ne_zero_of_odd_card {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K)) :
    (2 : K) ≠ 0 := by
  intro h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h
  have h2 := FiniteField.even_card_of_char_two (ringChar.eq K 2)
  rw [Nat.card_eq_fintype_card] at hodd
  exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_iff.mpr h2)

theorem card_statedProj_statedSp_two_mul_two {K : Type} [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) :
    Nat.card (StatedProj (StatedSp 2 K)) * 2 =
      Nat.card K ^ 4 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1)) := by
  rw [ClassicalInvolution.card_statedProj_statedSp_of_two_ne_zero (two_ne_zero_of_odd_card hodd)
    (by norm_num), show Finset.Icc 1 2 = {1, 2} by rfl, Finset.prod_pair (by norm_num)]
  norm_num

theorem not_psp4_of_lieModel_psl_three {X : Type} [Group X] {n : ℕ} (hn : 3 ≤ n)
    (hX : Blueprint.LieModel X .PSL 3 2 n) :
    ¬ ∃ (K : Type) (_ : Field K) (_ : Finite K), Odd (Nat.card K) ∧
      Nonempty (X ≃* StatedProj (StatedSp 2 K)) := by
  rintro ⟨K, _, _, hodd, ⟨e⟩⟩
  have hv := padicValNat_card_of_lieModel_psl_three (by omega) hX
  have hlt := card_lt_of_lieModel_psl_three hX
  have hc := card_statedProj_statedSp_two_mul_two hodd
  rw [← Nat.card_congr e.toEquiv] at hc
  have hq3 : 3 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    obtain ⟨m, hm⟩ := hodd
    omega
  by_cases h5 : 5 ≤ Nat.card K
  · have hc' : Nat.card X * 2 = Nat.card K ^ (2 ^ 2) *
        ∏ j ∈ Finset.Icc 1 2, (Nat.card K ^ (2 * j) - 1) := by
      rw [hc, show Finset.Icc 1 2 = {1, 2} by rfl, Finset.prod_pair (by norm_num)]
      norm_num
    have h := RankThree.PartTwo.KFacts.OddChar.two_pow_le_of_mul_two_eq_spOrd hodd hq3
      (Or.inr ⟨rfl, h5⟩) hc'
    rw [hv] at h
    have h3 : Nat.card X ^ 3 < 2 ^ (8 * (3 * n)) :=
      calc Nat.card X ^ 3 < (2 ^ (8 * n)) ^ 3 := Nat.pow_lt_pow_left hlt (by norm_num)
        _ = 2 ^ (8 * (3 * n)) := by rw [← pow_mul]; ring_nf
    omega
  · have hq : Nat.card K = 3 := by obtain ⟨m, hm⟩ := hodd; omega
    rw [hq] at hc
    have hN : Nat.card X = 25920 := by norm_num at hc; omega
    rw [hN] at hv
    have h6 : padicValNat 2 25920 = 6 := by
      rw [show (25920 : ℕ) = 2 ^ 6 * 405 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
        padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
    omega

theorem not_psp4_of_card {X : Type} [Group X] {N : ℕ} (hX : Nat.card X = N)
    (hN : N * 2 < 83521 * 288 * 83520)
    (hne : ∀ q : ℕ, 3 ≤ q → q ≤ 15 → N * 2 ≠ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))) :
    ¬ ∃ (K : Type) (_ : Field K) (_ : Finite K), Odd (Nat.card K) ∧
      Nonempty (X ≃* StatedProj (StatedSp 2 K)) := by
  rintro ⟨K, _, _, hodd, ⟨e⟩⟩
  have hc := card_statedProj_statedSp_two_mul_two hodd
  rw [← Nat.card_congr e.toEquiv, hX] at hc
  have hq1 := Finite.one_lt_card (α := K)
  obtain ⟨k, hk⟩ := hodd
  generalize Nat.card K = q at hc hk hq1
  have hq3 : 3 ≤ q := by omega
  by_cases h17 : 17 ≤ q
  · have h4 : 83521 ≤ q ^ 4 := by
      calc (83521 : ℕ) = 17 ^ 4 := by norm_num
        _ ≤ q ^ 4 := Nat.pow_le_pow_left h17 4
    have h2 : 288 ≤ q ^ 2 - 1 := by
      have : 17 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left h17 2
      omega
    have h4' : 83520 ≤ q ^ 4 - 1 := by omega
    have := Nat.mul_le_mul h4 (Nat.mul_le_mul h2 h4')
    rw [← hc] at this
    omega
  · exact hne q hq3 (by omega) hc

theorem not_psp4_of_suz {X : Type} [Group X]
    (h : Blueprint.NativeSporadic.IsSporadic X .Suz) :
    ¬ ∃ (K : Type) (_ : Field K) (_ : Finite K), Odd (Nat.card K) ∧
      Nonempty (X ≃* StatedProj (StatedSp 2 K)) := by
  obtain ⟨f⟩ := h
  refine not_psp4_of_card ((Nat.card_congr f.toEquiv).trans Sporadic.Suz.card_Suz)
    (by norm_num) fun q h3 h15 => ?_
  interval_cases q <;> norm_num

theorem not_psp4_of_onan {X : Type} [Group X]
    (h : Blueprint.NativeSporadic.IsSporadic X .ONan) :
    ¬ ∃ (K : Type) (_ : Field K) (_ : Finite K), Odd (Nat.card K) ∧
      Nonempty (X ≃* StatedProj (StatedSp 2 K)) := by
  obtain ⟨f⟩ := h
  refine not_psp4_of_card ((Nat.card_congr f.toEquiv).trans Sporadic.ON.card_ON)
    (by norm_num) fun q h3 h15 => ?_
  interval_cases q <;> norm_num

end CFSG.ComponentClassification.GrSLit.L34Sec5S
