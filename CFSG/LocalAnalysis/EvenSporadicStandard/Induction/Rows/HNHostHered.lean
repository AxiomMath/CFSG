module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Setting
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.UHered

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic

@[expose] def TwoHSHostAt (Y : Type) [Group Y] [Finite Y] : Prop :=
  ∀ (N' : Subgroup Y), FStarSimple N' → N'.index ≤ 2 →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y → ∀ P : Subgroup Y, SolStd P →
      CFSG.IsQuasisimple ↥P → Nat.card ↥(center ↥P) = 2 → IsSporadic (↥P ⧸ center ↥P) .HS →
        IsSporadic ↥N' .HN

@[expose] def TwoHSHostHered : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Balance.UHered Y → TwoHSHostAt Y

end CFSG.EvenSporadicStandard.Induction
