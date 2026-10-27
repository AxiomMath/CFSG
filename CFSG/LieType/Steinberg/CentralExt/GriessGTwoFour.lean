module

public import CFSG.LieType.Steinberg.CentralExt.GriessSmallExceptional
public import CFSG.LieType.Multipliers.G24Cover

public section

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Multiplier

namespace CFSG.LieType.Steinberg.CentralExt.GriessExceptional

theorem g2_four_card_griessHopfMultiplier {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) :
    commutator (AdjointQuotient .G2 K) = ⊤ ∧
      Nat.card (CFSG.Open.griessHopfMultiplier (AdjointQuotient .G2 K)) = 2 := by
  refine ⟨(G2Four.g2_four_hopfMultiplier hK).1, ?_⟩
  rw [Nat.card_congr (griessHopfMultiplierCongr ((QuotientGroup.quotientMulEquivOfEq
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot)).toEquiv]
  exact (CFSG.LieType.Multipliers.G24.multiplier_G2_four hK).1

variable {X : Type} [Group X]

theorem g2_four_native_row (h : ChevalleyExceptionalModel X .G2 2 2) :
    GriessAll.GriessRow X .G2 0 2 2 :=
  g2_four_native_row_of_card (fun _ _ _ hK => (g2_four_card_griessHopfMultiplier hK).2)
    (fun _ _ _ hK => (g2_four_card_griessHopfMultiplier hK).1) h

section TauCeti


theorem g2_four_row (hmodel : CFSG.Models.LieModel X .G2 0 2 2) :
    GriessAll.GriessRow X .G2 0 2 2 :=
  g2_four_row_of_card (fun _ _ _ hK => (g2_four_card_griessHopfMultiplier hK).2)
    (fun _ _ _ hK => (g2_four_card_griessHopfMultiplier hK).1) hmodel

end TauCeti

end CFSG.LieType.Steinberg.CentralExt.GriessExceptional
