module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcSylowN
public import CFSG.RankThree.Chevalley.EWeylLengthPolynomials

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Curtis.UnitaryLevi

theorem card_weylGroup_E7' :
    Nat.card (WeylGroup .E7) = 2903040 := by
  have : Fintype (WeylGroup .E7) := Fintype.ofFinite _
  have h := CFSG.RankThree.Chevalley.sum_length_E7_eq 1
  simp at h
  rw [Nat.card_eq_fintype_card, h]

theorem card_weylGroup_E8' :
    Nat.card (WeylGroup .E8) = 696729600 := by
  have : Fintype (WeylGroup .E8) := Fintype.ofFinite _
  have h := CFSG.RankThree.Chevalley.sum_length_E8_eq 1
  simp at h
  rw [Nat.card_eq_fintype_card, h]

private lemma padicValNat_three_eight : padicValNat 3 8 = 0 :=
  padicValNat.eq_zero_of_not_dvd (by norm_num)

private lemma padicValNat_three_two : padicValNat 3 2 = 0 :=
  padicValNat.eq_zero_of_not_dvd (by norm_num)

private lemma padicValNat_three_ten : padicValNat 3 10 = 0 :=
  padicValNat.eq_zero_of_not_dvd (by norm_num)

private lemma padicValNat_three_fourteen : padicValNat 3 14 = 0 :=
  padicValNat.eq_zero_of_not_dvd (by norm_num)

private lemma padicValNat_three_twenty : padicValNat 3 20 = 0 :=
  padicValNat.eq_zero_of_not_dvd (by norm_num)

private lemma padicValNat_three_six : padicValNat 3 6 = 1 := by
  rw [show (6 : ℕ) = 3 * 2 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat_self, padicValNat_three_two]

private lemma padicValNat_three_twelve : padicValNat 3 12 = 1 := by
  rw [show (12 : ℕ) = 3 * 4 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat_self, padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 4)]

private lemma padicValNat_three_eighteen : padicValNat 3 18 = 2 := by
  rw [show (18 : ℕ) = 3 ^ 2 * 2 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat.prime_pow, padicValNat_three_two]

private lemma padicValNat_three_twentyfour : padicValNat 3 24 = 1 := by
  rw [show (24 : ℕ) = 3 * 8 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat_self, padicValNat_three_eight]

private lemma padicValNat_three_thirty : padicValNat 3 30 = 1 := by
  rw [show (30 : ℕ) = 3 * 10 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat_self, padicValNat_three_ten]

private lemma sub_one_pos {q : ℕ} (hq : 1 < q) {n : ℕ} (hn : n ≠ 0) : 0 < q ^ n - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow hn hq)

theorem padicValNat_three_ordE7 {q : ℕ} (hq : 1 < q) (h3 : 3 ∣ q - 1) :
    padicValNat 3 (CFSG.Open.ordE7 q) = 7 * padicValNat 3 (q - 1) + 4 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnq : ¬ 3 ∣ q := by omega
  have h18 := sub_one_pos hq (n := 18) (by norm_num)
  have h14 := sub_one_pos hq (n := 14) (by norm_num)
  have h12 := sub_one_pos hq (n := 12) (by norm_num)
  have h10 := sub_one_pos hq (n := 10) (by norm_num)
  have h8 := sub_one_pos hq (n := 8) (by norm_num)
  have h6 := sub_one_pos hq (n := 6) (by norm_num)
  have h2 := sub_one_pos hq (n := 2) (by norm_num)
  have hX : q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
      (q ^ 6 - 1) * (q ^ 2 - 1) ≠ 0 := by positivity
  have hdvd : Nat.gcd 2 (q - 1) ∣ q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) *
      (q ^ 10 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1) := by
    refine Dvd.dvd.mul_left ?_ _
    have := Nat.sub_dvd_pow_sub_pow q 1 2
    rw [one_pow] at this
    exact (Nat.gcd_dvd_right 2 (q - 1)).trans this
  have hg : padicValNat 3 (Nat.gcd 2 (q - 1)) = 0 :=
    padicValNat.eq_zero_of_not_dvd fun h => by
      have := h.trans (Nat.gcd_dvd_left 2 (q - 1))
      omega
  have hgpos : Nat.gcd 2 (q - 1) ≠ 0 := (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne'
  have hmul := Nat.div_mul_cancel hdvd
  have hne : (q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) *
      (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)) / Nat.gcd 2 (q - 1) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    exact hX hmul.symm
  have key := congrArg (padicValNat 3) hmul
  rw [padicValNat.mul hne hgpos, hg, add_zero] at key
  unfold CFSG.Open.ordE7
  rw [key, padicValNat.mul (by positivity) h2.ne', padicValNat.mul (by positivity) h6.ne',
    padicValNat.mul (by positivity) h8.ne', padicValNat.mul (by positivity) h10.ne',
    padicValNat.mul (by positivity) h12.ne', padicValNat.mul (by positivity) h14.ne',
    padicValNat.mul (by positivity) h18.ne',
    padicValNat.pow q 63, padicValNat.eq_zero_of_not_dvd hnq,
    padicValNat_three_pow_sub_one hq h3 (by norm_num : 18 ≠ 0),
    padicValNat_three_pow_sub_one hq h3 (by norm_num : 14 ≠ 0),
    padicValNat_three_pow_sub_one hq h3 (by norm_num : 12 ≠ 0),
    padicValNat_three_pow_sub_one hq h3 (by norm_num : 10 ≠ 0),
    padicValNat_three_pow_sub_one hq h3 (by norm_num : 8 ≠ 0),
    padicValNat_three_pow_sub_one hq h3 (by norm_num : 6 ≠ 0),
    padicValNat_three_pow_sub_one hq h3 (by norm_num : 2 ≠ 0),
    padicValNat_three_eighteen, padicValNat_three_fourteen, padicValNat_three_twelve,
    padicValNat_three_ten, padicValNat_three_eight, padicValNat_three_six,
    padicValNat_three_two]
  omega

theorem padicValNat_three_ordE8 {q : ℕ} (hq : 1 < q) (h3 : 3 ∣ q - 1) :
    padicValNat 3 (CFSG.Open.ordE8 q) = 8 * padicValNat 3 (q - 1) + 5 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnq : ¬ 3 ∣ q := by omega
  have h30 := sub_one_pos hq (n := 30) (by norm_num)
  have h24 := sub_one_pos hq (n := 24) (by norm_num)
  have h20 := sub_one_pos hq (n := 20) (by norm_num)
  have h18 := sub_one_pos hq (n := 18) (by norm_num)
  have h14 := sub_one_pos hq (n := 14) (by norm_num)
  have h12 := sub_one_pos hq (n := 12) (by norm_num)
  have h8 := sub_one_pos hq (n := 8) (by norm_num)
  have h2 := sub_one_pos hq (n := 2) (by norm_num)
  unfold CFSG.Open.ordE8
  rw [padicValNat.mul (by positivity) h2.ne', padicValNat.mul (by positivity) h8.ne',
    padicValNat.mul (by positivity) h12.ne', padicValNat.mul (by positivity) h14.ne',
    padicValNat.mul (by positivity) h18.ne', padicValNat.mul (by positivity) h20.ne',
    padicValNat.mul (by positivity) h24.ne', padicValNat.mul (by positivity) h30.ne',
    padicValNat.pow q 120, padicValNat.eq_zero_of_not_dvd hnq,
    padicValNat_three_pow_sub_one hq h3 (by norm_num : 30 ≠ 0),
    padicValNat_three_pow_sub_one hq h3 (by norm_num : 24 ≠ 0),
    padicValNat_three_pow_sub_one hq h3 (by norm_num : 20 ≠ 0),
    padicValNat_three_pow_sub_one hq h3 (by norm_num : 18 ≠ 0),
    padicValNat_three_pow_sub_one hq h3 (by norm_num : 14 ≠ 0),
    padicValNat_three_pow_sub_one hq h3 (by norm_num : 12 ≠ 0),
    padicValNat_three_pow_sub_one hq h3 (by norm_num : 8 ≠ 0),
    padicValNat_three_pow_sub_one hq h3 (by norm_num : 2 ≠ 0),
    padicValNat_three_thirty, padicValNat_three_twentyfour, padicValNat_three_twenty,
    padicValNat_three_eighteen, padicValNat_three_fourteen, padicValNat_three_twelve,
    padicValNat_three_eight, padicValNat_three_two]
  omega

theorem exists_sylow_three_le_monomialSub_E7 (K : Type) [Field K] [Finite K]
    (h3 : 3 ∣ Nat.card K - 1) :
    ∃ P : Sylow 3 (adjointGroup .E7 K), (P : Subgroup (adjointGroup .E7 K)) ≤ monomialSub .E7 K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : 1 < Nat.card K := Finite.one_lt_card
  refine exists_sylow_three_le_of_factorization_eq _ ?_
  have hT := CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_E7 (K := K)
  have hT3 : padicValNat 3 (Nat.card (torusGroup .E7 K)) = 7 * padicValNat 3 (Nat.card K - 1) := by
    have h := congrArg (padicValNat 3) hT
    have hne : Nat.card (torusGroup .E7 K) ≠ 0 := Nat.card_pos.ne'
    have hg : (Nat.card K - 1).gcd 2 ≠ 0 := (Nat.gcd_pos_of_pos_right _ (by norm_num)).ne'
    rw [padicValNat.mul hne hg, padicValNat.pow (Nat.card K - 1) 7,
      padicValNat.eq_zero_of_not_dvd (p := 3) (n := (Nat.card K - 1).gcd 2) fun h' => by
        have := h'.trans (Nat.gcd_dvd_right (Nat.card K - 1) 2)
        omega] at h
    omega
  rw [Nat.factorization_def _ Nat.prime_three, Nat.factorization_def _ Nat.prime_three,
    card_monomialSub_eq, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E7,
    card_weylGroup_E7', padicValNat_three_ordE7 hq h3,
    padicValNat.mul Nat.card_pos.ne' (by norm_num), hT3]
  have e : padicValNat 3 2903040 = 4 := by
    rw [show (2903040 : ℕ) = 3 ^ 4 * 35840 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  rw [e]

theorem exists_sylow_three_le_monomialSub_E8 (K : Type) [Field K] [Finite K]
    (h3 : 3 ∣ Nat.card K - 1) :
    ∃ P : Sylow 3 (adjointGroup .E8 K), (P : Subgroup (adjointGroup .E8 K)) ≤ monomialSub .E8 K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : 1 < Nat.card K := Finite.one_lt_card
  refine exists_sylow_three_le_of_factorization_eq _ ?_
  rw [Nat.factorization_def _ Nat.prime_three, Nat.factorization_def _ Nat.prime_three,
    card_monomialSub_eq, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8,
    CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_E8,
    card_weylGroup_E8', padicValNat_three_ordE8 hq h3,
    padicValNat.mul (pow_ne_zero _ (by omega)) (by norm_num), padicValNat.pow (Nat.card K - 1) 8]
  have e : padicValNat 3 696729600 = 5 := by
    rw [show (696729600 : ℕ) = 3 ^ 5 * 2867200 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  rw [e]

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

end
