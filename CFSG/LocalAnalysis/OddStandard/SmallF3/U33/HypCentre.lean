module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Blocks
public import CFSG.ClassicalInvolution.Orders.Classical

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup CFSG.Blueprint

private theorem card_lieModel_PSU_3_3 {Q : Type} [Group Q] (h : LieModel Q .PSU 3 3 1) :
    Nat.card Q = 6048 := by
  have hc := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Q)
      (show (3 : ℕ) ≠ 2 by norm_num) (h.statedClassicalModel_of_ne_zero (by norm_num))).2.1 rfl
  rw [hc]
  decide +kernel

private theorem card_lieModel_PSU_4_3 {Q : Type} [Group Q] (h : LieModel Q .PSU 4 3 1) :
    Nat.card Q = 3265920 := by
  have hc := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Q)
      (show (3 : ℕ) ≠ 2 by norm_num) (h.statedClassicalModel_of_ne_zero (by norm_num))).2.1 rfl
  rw [hc]
  decide +kernel

theorem center_eq_bot_of_psu33 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hC : SmallF3Cyclic G L) (hQ : LieModel (L ⧸ center L) .PSU 3 3 1) : center L = ⊥ := by
  rcases hC.centre with h | ⟨h4, _⟩
  · exact h
  · exfalso
    have h1 : Nat.card (L ⧸ center L) = 6048 := card_lieModel_PSU_3_3 hQ
    have h2 : Nat.card (L ⧸ center L) = 3265920 := card_lieModel_PSU_4_3 h4
    omega

end CFSG.OddStandard.SmallF3.HarrisU33
