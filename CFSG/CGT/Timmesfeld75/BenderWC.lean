module

public import CFSG.CGT.Timmesfeld75.Config
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

@[expose] def BenderWCInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.BenderSuzuki.IsBenderGroup K →
    ∀ T : Subgroup K, IsWC T → T ≠ ⊥ → ∀ g : K, conjSubgroup g T ≠ T →
      normIn T (conjSubgroup g T) = ⊥

end CFSG.CGT.Timmesfeld75
