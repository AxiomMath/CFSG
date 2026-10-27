module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Defs

public section

namespace CFSG.EvenSporadicStandard.HNRecog

@[expose] def SegevUniqueness : Prop :=
  ∀ (G G' : Type) [Group G] [Finite G] [IsSimpleGroup G] [Group G'] [Finite G']
    [IsSimpleGroup G'] (a z : G) (a' z' : G'),
    IsF5Type a z → IsF5Type a' z' → Nonempty (G ≃* G')

end CFSG.EvenSporadicStandard.HNRecog
