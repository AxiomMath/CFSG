module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.UHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Setting

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78

@[expose] def RuBalanceAt (H : Type) [Group H] [Finite H] : Prop :=
  ∀ (N : Subgroup H), FStarSimple N → N.index ≤ 2 →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → ∀ (M : Subgroup H) (v : H),
      orderOf v = 2 → IsCompIn M (centralizer ({v} : Set H)) → OddCover .Ru M →
        (∀ P : Sylow 2 (centralizer (M : Set H)), Nat.card P = 2) →
          centralizer ({v} : Set H) = M ⊔ zpowers v

@[expose] def RuBalanceHered : Prop :=
  ∀ (H : Type) [Group H] [Finite H], Balance.UHered H → RuBalanceAt H

end CFSG.EvenSporadicStandard.Induction
