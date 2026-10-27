module

public import CFSG.LieType.Steinberg.CentralExt.GriessSmallExceptional
public import CFSG.LieType.Steinberg.CentralExt.G2ThreeMultiplier
public import CFSG.LieType.Multipliers.G23Cover

public section

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Multiplier

namespace CFSG.LieType.Steinberg.CentralExt.GriessExceptional

theorem g2_three_card_griessHopfMultiplier {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3) :
    commutator (AdjointQuotient .G2 K) = ⊤ ∧
      Nat.card (CFSG.Open.griessHopfMultiplier (AdjointQuotient .G2 K)) = 3 := by
  obtain ⟨hperf, hle⟩ := FieldThree.g2_three_hopfMultiplier hK
  have hdvd := CFSG.LieType.Multipliers.G23.three_dvd_card_griessHopfMultiplier_adjointQuotient hK
  have : Group.IsPerfect (AdjointQuotient .G2 K) := ⟨hperf⟩
  have : Finite (CFSG.RankThree.PerfectCover.hopfMultiplier (AdjointQuotient .G2 K)) :=
    CFSG.RankThree.PerfectCover.finite_hopfMultiplier inferInstance
  have : Finite (CFSG.Open.griessHopfMultiplier (AdjointQuotient .G2 K)) :=
    Finite.of_equiv _ (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).symm.toEquiv
  exact ⟨hperf, le_antisymm hle (Nat.le_of_dvd Nat.card_pos hdvd)⟩

variable {X : Type} [Group X]

theorem g2_three_native_row (h : ChevalleyExceptionalModel X .G2 3 1) :
    GriessAll.GriessRow X .G2 0 3 1 :=
  g2_three_native_row_of_card (fun _ _ _ hK => (g2_three_card_griessHopfMultiplier hK).2)
    (fun _ _ _ hK => (g2_three_card_griessHopfMultiplier hK).1) h

section TauCeti


theorem g2_three_row (hmodel : CFSG.Models.LieModel X .G2 0 3 1) :
    GriessAll.GriessRow X .G2 0 3 1 :=
  g2_three_row_of_card (fun _ _ _ hK => (g2_three_card_griessHopfMultiplier hK).2)
    (fun _ _ _ hK => (g2_three_card_griessHopfMultiplier hK).1) hmodel

end TauCeti

end CFSG.LieType.Steinberg.CentralExt.GriessExceptional
