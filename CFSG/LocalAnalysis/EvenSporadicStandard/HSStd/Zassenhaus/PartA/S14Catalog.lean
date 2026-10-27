module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONanProps

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup

@[expose] def ONanNoSL29Y : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (N : Subgroup Y), N.Normal → centralizer (N : Set Y) ≤ N →
    ONanList ↥N → ∀ H : Subgroup Y, ⁅H, H⁆ = H → Nat.card (center ↥H) = 2 →
      Nonempty (↥H ⧸ center ↥H ≃* alternatingGroup (Fin 6)) → False

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
