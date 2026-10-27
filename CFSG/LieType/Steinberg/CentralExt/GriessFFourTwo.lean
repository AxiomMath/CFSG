module

public import CFSG.LieType.Steinberg.CentralExt.GriessSmallExceptional
public import CFSG.LieType.Steinberg.CentralExt.F4TwoMultiplier
public import CFSG.LieType.Multipliers.F42Cover

public section

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Multiplier

namespace CFSG.LieType.Steinberg.CentralExt.GriessExceptional

theorem f4_two_card_griessHopfMultiplier {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    commutator (AdjointQuotient .F4 K) = ⊤ ∧
      Nat.card (CFSG.Open.griessHopfMultiplier (AdjointQuotient .F4 K)) = 2 := by
  obtain ⟨hperf, hle⟩ := F4Two.f4_two_hopfMultiplier hK
  have hdvd := CFSG.LieType.Multipliers.F42.two_dvd_card_griessHopfMultiplier_adjointQuotient hK
  have : Group.IsPerfect (AdjointQuotient .F4 K) := ⟨hperf⟩
  have : Finite (CFSG.RankThree.PerfectCover.hopfMultiplier (AdjointQuotient .F4 K)) :=
    CFSG.RankThree.PerfectCover.finite_hopfMultiplier inferInstance
  have : Finite (CFSG.Open.griessHopfMultiplier (AdjointQuotient .F4 K)) :=
    Finite.of_equiv _ (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).symm.toEquiv
  exact ⟨hperf, le_antisymm hle (Nat.le_of_dvd Nat.card_pos hdvd)⟩

variable {X : Type} [Group X]

theorem f4_two_native_row (h : ChevalleyExceptionalModel X .F4 2 1) :
    GriessAll.GriessRow X .F4 0 2 1 :=
  f4_two_native_row_of_card (fun _ _ _ hK => (f4_two_card_griessHopfMultiplier hK).2)
    (fun _ _ _ hK => (f4_two_card_griessHopfMultiplier hK).1) h

section TauCeti


theorem f4_two_row (hmodel : CFSG.Models.LieModel X .F4 0 2 1) :
    GriessAll.GriessRow X .F4 0 2 1 :=
  f4_two_row_of_card (fun _ _ _ hK => (f4_two_card_griessHopfMultiplier hK).2)
    (fun _ _ _ hK => (f4_two_card_griessHopfMultiplier hK).1) hmodel

end TauCeti

end CFSG.LieType.Steinberg.CentralExt.GriessExceptional
