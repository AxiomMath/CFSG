module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Thm24ThreeSimpleCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuThm54

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp

@[expose] def Sol78Thm54ReachIndex (k : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (N' : Subgroup Y), FStarSimple N' → N'.index = k →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y →
    ∀ P : Subgroup Y, SolStd P → CFSG.IsQuasisimple ↥P →
      Sol78Thm54Types (↥P ⧸ center ↥P) → ¬ 29 ∣ Nat.card (↥P ⧸ center ↥P) →
        (Sol78Thm54Types ↥N' ∧ ¬ 29 ∣ Nat.card ↥N') ∨ (SuzukiModel ↥P 2 3 ∧ IsSporadic ↥N' .Ru)

end CFSG.EvenSporadicStandard.Induction
