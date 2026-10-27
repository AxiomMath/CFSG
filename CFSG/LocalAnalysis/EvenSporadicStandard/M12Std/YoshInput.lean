module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Schreier.Co3FaithfulData

public section

namespace CFSG.EvenSporadicStandard.M12Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Schreier.Co3

@[expose] def FusionSimple (K : Type) [Group K] : Prop :=
  (∀ N : Subgroup K, N.Normal → Odd (Nat.card N) → N = ⊥) ∧ center K = ⊥ ∧
    ∀ (N : Subgroup K) [N.Normal], IsPGroup 2 (K ⧸ N) → N = ⊤

end CFSG.EvenSporadicStandard.M12Std
