module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.UHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Thm24ThreeSimpleCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuThm54

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp
open CFSG.SignalizerFunctorTheorem (IsSectionOf)

@[expose] def Sol78Thm54ReachAt (Y : Type) [Group Y] [Finite Y] : Prop :=
  ∀ (N' : Subgroup Y), FStarSimple N' → N'.index ≤ 2 →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y →
    ∀ P : Subgroup Y, SolStd P → CFSG.IsQuasisimple ↥P →
      Sol78Thm54Types (↥P ⧸ center ↥P) → ¬ 29 ∣ Nat.card (↥P ⧸ center ↥P) →
        (Sol78Thm54Types ↥N' ∧ ¬ 29 ∣ Nat.card ↥N') ∨ (SuzukiModel ↥P 2 3 ∧ IsSporadic ↥N' .Ru)

@[expose] def Sol78Thm54ReachHered : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Balance.UHered Y → Sol78Thm54ReachAt Y

end CFSG.EvenSporadicStandard.Induction
