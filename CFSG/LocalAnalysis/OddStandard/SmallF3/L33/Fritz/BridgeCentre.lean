module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Blocks
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.OddStandard.SmallF3.L33

open Subgroup CFSG.Blueprint

theorem center_eq_bot_of_l33 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hS : SmallF3Cyclic G L) (hL : LieModel (L ⧸ center L) .PSL 3 3 1) : center L = ⊥ := by
  rcases hS.centre with h | ⟨hU, -⟩
  · exact h
  · exfalso
    have h1 := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_three
      (hL.statedClassicalModel_of_ne_zero (by norm_num))
    have h2 := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_four_three
      (hU.statedClassicalModel_of_ne_zero (by norm_num))
    omega

end CFSG.OddStandard.SmallF3.L33
