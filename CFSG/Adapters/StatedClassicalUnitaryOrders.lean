module

public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.Open.StatedAPI

open CFSG.Assembly.LowTwoRank

variable {X : Type} [Group X]

theorem card_of_statedClassicalModel_psu {k p e : ℕ} (hk : 2 ≤ k)
    (h : StatedClassicalModel X .PSU k p e) :
    Nat.card X = (p ^ e) ^ (k * (k - 1) / 2) *
      (∏ i ∈ Finset.Icc 2 k, (((p ^ e : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) / Nat.gcd k (p ^ e + 1) := by
  obtain ⟨⟨hp, he, -⟩, K, _, _, hK, ⟨φ⟩⟩ := h
  rw [Nat.card_congr φ.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU hp he hK hk]

theorem card_of_statedClassicalModel_psu_three_three (h : StatedClassicalModel X .PSU 3 3 1) :
    Nat.card X = 6048 := by
  rw [card_of_statedClassicalModel_psu (by norm_num) h]
  decide

theorem card_of_statedClassicalModel_psu_three_four (h : StatedClassicalModel X .PSU 3 2 2) :
    Nat.card X = 62400 := by
  rw [card_of_statedClassicalModel_psu (by norm_num) h]
  decide

theorem card_of_statedClassicalModel_psu_three_five (h : StatedClassicalModel X .PSU 3 5 1) :
    Nat.card X = 126000 := by
  rw [card_of_statedClassicalModel_psu (by norm_num) h]
  decide

theorem card_of_statedClassicalModel_psu_three_seven (h : StatedClassicalModel X .PSU 3 7 1) :
    Nat.card X = 5663616 := by
  rw [card_of_statedClassicalModel_psu (by norm_num) h]
  decide

theorem card_of_statedClassicalModel_psu_three_eight (h : StatedClassicalModel X .PSU 3 2 3) :
    Nat.card X = 5515776 := by
  rw [card_of_statedClassicalModel_psu (by norm_num) h]
  decide

theorem card_of_statedClassicalModel_psu_four_two (h : StatedClassicalModel X .PSU 4 2 1) :
    Nat.card X = 25920 := by
  rw [card_of_statedClassicalModel_psu (by norm_num) h]
  decide

theorem card_of_statedClassicalModel_psu_four_three (h : StatedClassicalModel X .PSU 4 3 1) :
    Nat.card X = 3265920 := by
  rw [card_of_statedClassicalModel_psu (by norm_num) h]
  decide

theorem card_of_statedClassicalModel_psu_five_two (h : StatedClassicalModel X .PSU 5 2 1) :
    Nat.card X = 13685760 := by
  rw [card_of_statedClassicalModel_psu (by norm_num) h]
  decide

theorem card_of_statedClassicalModel_psu_six_two (h : StatedClassicalModel X .PSU 6 2 1) :
    Nat.card X = 9196830720 := by
  rw [card_of_statedClassicalModel_psu (by norm_num) h]
  decide

theorem card_of_statedClassicalModel_psu_four_four (h : StatedClassicalModel X .PSU 4 2 2) :
    Nat.card X = 1018368000 := by
  rw [card_of_statedClassicalModel_psu (by norm_num) h]
  decide

theorem card_of_statedClassicalModel_psu_five_four (h : StatedClassicalModel X .PSU 5 2 2) :
    Nat.card X = 53443952640000 := by
  rw [card_of_statedClassicalModel_psu (by norm_num) h]
  decide

end CFSG.Open.StatedAPI
