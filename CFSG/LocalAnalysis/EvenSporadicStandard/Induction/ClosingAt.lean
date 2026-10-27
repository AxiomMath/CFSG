module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Setting
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.UHered

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78

@[expose] def Sol78ClosingAt (S : List TauCeti.SporadicName)
    (Q : TauCeti.SporadicName → PairClass) (H : Type) [Group H] [Finite H] : Prop :=
  ∀ (N L K : Subgroup H) (t u : H) (s : TauCeti.SporadicName),
    s ∈ S → FStarSimple N → N.index ≤ 2 → CFSG.Assembly.KProper CFSG.Blueprint.Catalog H →
      OddCover s L →
      SolomonGlobalQ H L K t u → Q s H L K u → False

@[expose] def Sol78ClosingHered (S : List TauCeti.SporadicName)
    (Q : TauCeti.SporadicName → PairClass) : Prop :=
  ∀ (H : Type) [Group H] [Finite H], Balance.UHered H → Sol78ClosingAt S Q H

theorem Sol78Closing.hered {S : List TauCeti.SporadicName}
    {Q : TauCeti.SporadicName → PairClass} (h : Sol78Closing S Q) : Sol78ClosingHered S Q :=
  fun H _ _ _ => h H

end CFSG.EvenSporadicStandard.Induction
