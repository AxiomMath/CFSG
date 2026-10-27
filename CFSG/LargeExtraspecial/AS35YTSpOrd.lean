module

public import CFSG.LargeExtraspecial.AS35YN
public import CFSG.LargeExtraspecial.AS35YTOrd

public section

namespace CFSG.LargeExtraspecial.AS35YT

open CFSG.Blueprint

theorem one_le_two_pow_two_mul_sub_one {i : ℕ} (hi : 1 ≤ i) : 1 ≤ 2 ^ (2 * i) - 1 := by
  have : 2 ≤ 2 ^ (2 * i) := Nat.le_self_pow (by omega) 2
  omega

theorem spOrd_strictMono :
    StrictMono fun j : ℕ => 2 ^ (j ^ 2) * ∏ i ∈ Finset.Icc 1 j, (2 ^ (2 * i) - 1) := by
  refine strictMono_nat_of_lt_succ fun j => ?_
  have hP : 0 < ∏ i ∈ Finset.Icc 1 j, (2 ^ (2 * i) - 1) := Finset.prod_pos fun i hi =>
    one_le_two_pow_two_mul_sub_one (Finset.mem_Icc.mp hi).1
  have hPle : ∏ i ∈ Finset.Icc 1 j, (2 ^ (2 * i) - 1) ≤
      ∏ i ∈ Finset.Icc 1 (j + 1), (2 ^ (2 * i) - 1) :=
    Finset.prod_le_prod_of_subset_of_one_le (Finset.Icc_subset_Icc_right (by omega))
      fun i hi _ => one_le_two_pow_two_mul_sub_one (Finset.mem_Icc.mp hi).1
  have h2 : 2 ^ (j ^ 2) < 2 ^ ((j + 1) ^ 2) :=
    Nat.pow_lt_pow_right (by norm_num) (Nat.pow_lt_pow_left (by omega) (by norm_num))
  calc 2 ^ (j ^ 2) * ∏ i ∈ Finset.Icc 1 j, (2 ^ (2 * i) - 1)
      < 2 ^ ((j + 1) ^ 2) * ∏ i ∈ Finset.Icc 1 j, (2 ^ (2 * i) - 1) :=
        Nat.mul_lt_mul_of_pos_right h2 hP
    _ ≤ 2 ^ ((j + 1) ^ 2) * ∏ i ∈ Finset.Icc 1 (j + 1), (2 ^ (2 * i) - 1) :=
        Nat.mul_le_mul_left _ hPle

theorem le_of_spOrd_le {k j : ℕ}
    (h : 2 ^ (k ^ 2) * ∏ i ∈ Finset.Icc 1 k, (2 ^ (2 * i) - 1) ≤
      2 ^ (j ^ 2) * ∏ i ∈ Finset.Icc 1 j, (2 ^ (2 * i) - 1)) : k ≤ j :=
  spOrd_strictMono.le_iff_le.mp h

theorem spOrd_pred_lt_card_of_lieModel_POmega {X : Type} [Group X] {k : ℕ}
    (h : LieModel X .POmegaPlus k 2 1 ∨ LieModel X .POmegaMinus k 2 1) :
    2 ^ ((k - 1) ^ 2) * ∏ i ∈ Finset.Icc 1 (k - 1), (2 ^ (2 * i) - 1) < Nat.card X := by
  obtain ⟨hk, hX | hX⟩ := A2Mod.Ord.card_of_lieModel_POmega h
  all_goals
    have hP : 0 < ∏ i ∈ Finset.Icc 1 (k - 1), (2 ^ (2 * i) - 1) := Finset.prod_pos fun i hi =>
      one_le_two_pow_two_mul_sub_one (Finset.mem_Icc.mp hi).1
    have h1 : (k - 1) ^ 2 < k * (k - 1) := by
      rw [sq]
      exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    have h2 : 2 ^ ((k - 1) ^ 2) < 2 ^ (k * (k - 1)) := Nat.pow_lt_pow_right (by norm_num) h1
    have h3 : 2 ≤ 2 ^ k := Nat.le_self_pow (by omega) 2
  · rw [hX, A2Mod.Ord.ordD_two_eq (by omega)]
    exact Nat.mul_lt_mul_of_pos_right (lt_of_lt_of_le h2 (Nat.le_mul_of_pos_right _ (by omega)))
      hP
  · rw [hX, A2Mod.Ord.ordTwistedD_two_eq (by omega)]
    exact Nat.mul_lt_mul_of_pos_right (lt_of_lt_of_le h2 (Nat.le_mul_of_pos_right _ (by omega)))
      hP

theorem le_of_le_spOrd_of_POmega {X : Type} [Group X] {k j : ℕ}
    (h : LieModel X .POmegaPlus k 2 1 ∨ LieModel X .POmegaMinus k 2 1)
    (hj : Nat.card X ≤ 2 ^ (j ^ 2) * ∏ i ∈ Finset.Icc 1 j, (2 ^ (2 * i) - 1)) : k ≤ j := by
  have hk : 4 ≤ k := by
    rcases h with h | h
    · exact (A2Mod.Ord.card_of_lieModel_POmegaPlus h).1
    · exact (A2Mod.Ord.card_of_lieModel_POmegaMinus h).1
  by_contra hlt
  have h1 := AS35YN.spOrd_le (show j ≤ k - 1 by omega)
  have h2 := spOrd_pred_lt_card_of_lieModel_POmega h
  omega

theorem le_of_le_spOrd_of_PSp {X : Type} [Group X] {k j : ℕ} (h : LieModel X .PSp k 2 1)
    (hj : Nat.card X ≤ 2 ^ (j ^ 2) * ∏ i ∈ Finset.Icc 1 j, (2 ^ (2 * i) - 1)) : k ≤ j := by
  refine le_of_spOrd_le (le_trans (le_of_eq ?_) hj)
  rw [(A2Mod.Ord.card_of_lieModel_PSp h).2, ordBC_two_eq', sq]

theorem three_le_of_le_spOrd_of_PSL4 {X : Type} [Group X] {j : ℕ} (h : LieModel X .PSL 4 2 1)
    (hj : Nat.card X ≤ 2 ^ (j ^ 2) * ∏ i ∈ Finset.Icc 1 j, (2 ^ (2 * i) - 1)) : 3 ≤ j := by
  have hX : Nat.card X = 20160 := by
    rw [(A2Mod.Ord.card_of_lieModel_PSL h).2]
    decide
  by_contra hlt
  have h1 := AS35YN.spOrd_le (show j ≤ 2 by omega)
  have h2 : 2 ^ (2 ^ 2) * ∏ i ∈ Finset.Icc 1 2, (2 ^ (2 * i) - 1) = 720 := by decide
  omega

end CFSG.LargeExtraspecial.AS35YT
