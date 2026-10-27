module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFive
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.HardMathSupport.Timmesfeld.Proving

open CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem orderOf_natCast_zmod_five_of_dvd_add_one {n : ℕ} (h5 : 5 ∣ n + 1) :
    orderOf ((n : ℕ) : ZMod 5) = 2 := by
  have h0 : ((n + 1 : ℕ) : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h5
  rw [Nat.cast_add, Nat.cast_one] at h0
  have hn : ((n : ℕ) : ZMod 5) = -1 := eq_neg_of_add_eq_zero_left h0
  rw [hn]
  exact orderOf_eq_prime (by decide) (by decide)

theorem not_five_dvd_of_dvd_add_one {n : ℕ} (h5 : 5 ∣ n + 1) : ¬ 5 ∣ n := by
  intro h
  have h1 : 5 ∣ n + 1 - n := Nat.dvd_sub h5 h
  rw [show n + 1 - n = 1 by omega] at h1
  norm_num at h1

theorem not_five_dvd_sub_one_of_dvd_add_one {n : ℕ} (h5 : 5 ∣ n + 1) : ¬ 5 ∣ n - 1 := by
  rintro ⟨c, hc⟩
  obtain ⟨d, hd⟩ := h5
  omega

theorem not_five_dvd_pow_sub_one_of_odd {n d : ℕ} (h5 : 5 ∣ n + 1) (hd : Odd d) :
    ¬ 5 ∣ n ^ d - 1 := by
  intro h
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num at h5
    · exact hn
  have h0 : ((n ^ d - 1 : ℕ) : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
  have h1 : ((n + 1 : ℕ) : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h5
  rw [Nat.cast_add, Nat.cast_one] at h1
  have hn : ((n : ℕ) : ZMod 5) = -1 := eq_neg_of_add_eq_zero_left h1
  have hpow : ((-1 : ZMod 5)) ^ d = -1 := hd.neg_one_pow
  rw [Nat.cast_sub (Nat.one_le_pow d n hn1), Nat.cast_pow, Nat.cast_one, hn, hpow] at h0
  exact absurd h0 (by decide)

theorem ordProj_five_pow_sub_one_of_dvd_add_one {K : Type} [Field K] [Finite K]
    (h5 : 5 ∣ Nat.card K + 1) {d k : ℕ} (hdk : d = 2 * k) (hk : k ≠ 0) :
    5 ^ (Nat.card K ^ d - 1).factorization 5 =
      5 ^ (Nat.card K + 1).factorization 5 * 5 ^ k.factorization 5 := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have h := ordProj_pow_sub_one_of_dvd Nat.prime_five (by norm_num)
    (not_five_dvd_of_dvd_add_one h5) hq2 (orderOf_natCast_zmod_five_of_dvd_add_one h5) hk
  rw [hdk, h]
  congr 1
  have hsq : Nat.card K ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) := by
    zify [Nat.one_le_pow 2 (Nat.card K) (by omega), (by omega : 1 ≤ Nat.card K)]
    ring
  rw [hsq, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (not_five_dvd_sub_one_of_dvd_add_one h5), add_zero]


theorem factorization_five_card_adjointGroup_E7_of_dvd_add_one (K : Type) [Field K] [Finite K]
    (h5 : 5 ∣ Nat.card K + 1) :
    (Nat.card (adjointGroup Tag.E7 K)).factorization 5 =
      7 * (Nat.card K + 1).factorization 5 + 1 := by
  have h := ordProj_card_adjointGroup_E (τ := Tag.E7) (K := K) (by simp) Nat.prime_five
    (by norm_num) (not_five_dvd_of_dvd_add_one h5)
  simp only [degreesE, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  rw [ordProj_five_pow_sub_one_of_dvd_add_one h5 (d := 2) (k := 1) rfl one_ne_zero,
    ordProj_five_pow_sub_one_of_dvd_add_one h5 (d := 6) (k := 3) rfl (by norm_num),
    ordProj_five_pow_sub_one_of_dvd_add_one h5 (d := 8) (k := 4) rfl (by norm_num),
    ordProj_five_pow_sub_one_of_dvd_add_one h5 (d := 10) (k := 5) rfl (by norm_num),
    ordProj_five_pow_sub_one_of_dvd_add_one h5 (d := 12) (k := 6) rfl (by norm_num),
    ordProj_five_pow_sub_one_of_dvd_add_one h5 (d := 14) (k := 7) rfl (by norm_num),
    ordProj_five_pow_sub_one_of_dvd_add_one h5 (d := 18) (k := 9) rfl (by norm_num),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 1),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 3),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 4),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 6),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 7),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 9),
    Nat.Prime.factorization_self Nat.prime_five] at h
  refine Nat.pow_right_injective (by norm_num : 2 ≤ 5) ?_
  change 5 ^ _ = 5 ^ _
  rw [h]
  ring

theorem factorization_five_card_adjointGroup_E6_of_dvd_add_one (K : Type) [Field K] [Finite K]
    (h5 : 5 ∣ Nat.card K + 1) :
    (Nat.card (adjointGroup Tag.E6 K)).factorization 5 = 4 * (Nat.card K + 1).factorization 5 := by
  have h := ordProj_card_adjointGroup_E (τ := Tag.E6) (K := K) (by simp) Nat.prime_five
    (by norm_num) (not_five_dvd_of_dvd_add_one h5)
  simp only [degreesE, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  rw [ordProj_five_pow_sub_one_of_dvd_add_one h5 (d := 2) (k := 1) rfl one_ne_zero,
    ordProj_eq_one_of_not_dvd' (not_five_dvd_pow_sub_one_of_odd h5 (by decide : Odd 5)),
    ordProj_five_pow_sub_one_of_dvd_add_one h5 (d := 6) (k := 3) rfl (by norm_num),
    ordProj_five_pow_sub_one_of_dvd_add_one h5 (d := 8) (k := 4) rfl (by norm_num),
    ordProj_eq_one_of_not_dvd' (not_five_dvd_pow_sub_one_of_odd h5 (by decide : Odd 9)),
    ordProj_five_pow_sub_one_of_dvd_add_one h5 (d := 12) (k := 6) rfl (by norm_num),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 1),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 3),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 4),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 6)] at h
  refine Nat.pow_right_injective (by norm_num : 2 ≤ 5) ?_
  change 5 ^ _ = 5 ^ _
  rw [h]
  ring

theorem factorization_five_card_adjointGroup_E8 (K : Type) [Field K] [Finite K]
    (h5 : 5 ∣ Nat.card K - 1) :
    (Nat.card (adjointGroup Tag.E8 K)).factorization 5 =
      8 * (Nat.card K - 1).factorization 5 + 2 := by
  have h := ordProj_card_adjointGroup_E (τ := Tag.E8) (K := K) (by simp) Nat.prime_five
    (by norm_num) (not_five_dvd_of_dvd_sub_one (Finite.one_lt_card (α := K)).le h5)
  simp only [degreesE, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  have h20 : 5 ^ (20 : ℕ).factorization 5 = 5 := by
    rw [show (20 : ℕ) = 4 * 5 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_five,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 4)]
    norm_num
  have h30 : 5 ^ (30 : ℕ).factorization 5 = 5 := by
    rw [show (30 : ℕ) = 6 * 5 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_five,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 6)]
    norm_num
  rw [ordProj_five_pow_sub_one h5 (by norm_num : (2 : ℕ) ≠ 0),
    ordProj_five_pow_sub_one h5 (by norm_num : (8 : ℕ) ≠ 0),
    ordProj_five_pow_sub_one h5 (by norm_num : (12 : ℕ) ≠ 0),
    ordProj_five_pow_sub_one h5 (by norm_num : (14 : ℕ) ≠ 0),
    ordProj_five_pow_sub_one h5 (by norm_num : (18 : ℕ) ≠ 0),
    ordProj_five_pow_sub_one h5 (by norm_num : (20 : ℕ) ≠ 0),
    ordProj_five_pow_sub_one h5 (by norm_num : (24 : ℕ) ≠ 0),
    ordProj_five_pow_sub_one h5 (by norm_num : (30 : ℕ) ≠ 0),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 2),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 8),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 12),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 14),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 18),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 24), h20, h30] at h
  refine Nat.pow_right_injective (by norm_num : 2 ≤ 5) ?_
  change 5 ^ _ = 5 ^ _
  rw [h]
  ring

theorem factorization_five_card_adjointGroup_E8_of_dvd_add_one (K : Type) [Field K] [Finite K]
    (h5 : 5 ∣ Nat.card K + 1) :
    (Nat.card (adjointGroup Tag.E8 K)).factorization 5 =
      8 * (Nat.card K + 1).factorization 5 + 2 := by
  have h := ordProj_card_adjointGroup_E (τ := Tag.E8) (K := K) (by simp) Nat.prime_five
    (by norm_num) (not_five_dvd_of_dvd_add_one h5)
  simp only [degreesE, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  have h10 : 5 ^ (10 : ℕ).factorization 5 = 5 := by
    rw [show (10 : ℕ) = 2 * 5 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_five,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 2)]
    norm_num
  have h15 : 5 ^ (15 : ℕ).factorization 5 = 5 := by
    rw [show (15 : ℕ) = 3 * 5 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_five,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 3)]
    norm_num
  rw [ordProj_five_pow_sub_one_of_dvd_add_one h5 (d := 2) (k := 1) rfl one_ne_zero,
    ordProj_five_pow_sub_one_of_dvd_add_one h5 (d := 8) (k := 4) rfl (by norm_num),
    ordProj_five_pow_sub_one_of_dvd_add_one h5 (d := 12) (k := 6) rfl (by norm_num),
    ordProj_five_pow_sub_one_of_dvd_add_one h5 (d := 14) (k := 7) rfl (by norm_num),
    ordProj_five_pow_sub_one_of_dvd_add_one h5 (d := 18) (k := 9) rfl (by norm_num),
    ordProj_five_pow_sub_one_of_dvd_add_one h5 (d := 20) (k := 10) rfl (by norm_num),
    ordProj_five_pow_sub_one_of_dvd_add_one h5 (d := 24) (k := 12) rfl (by norm_num),
    ordProj_five_pow_sub_one_of_dvd_add_one h5 (d := 30) (k := 15) rfl (by norm_num),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 1),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 4),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 6),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 7),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 9),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 12), h10, h15] at h
  refine Nat.pow_right_injective (by norm_num : 2 ≤ 5) ?_
  change 5 ^ _ = 5 ^ _
  rw [h]
  ring

end CFSG.HardMathSupport.Timmesfeld.Proving
