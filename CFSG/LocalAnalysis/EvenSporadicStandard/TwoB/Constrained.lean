module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Setting

public section

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup

@[expose] def DS81Lemma54 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t z : G),
    Setting G L t → CentralPair G L t z → IsTwoConstrained (centZ z)

end CFSG.EvenSporadicStandard.TwoB
