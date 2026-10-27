module

public import CFSG.ClassicalInvolution.Q3.Q3WShape
public import CFSG.ClassicalInvolution.Q3.Q3WALoc

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TC

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3.Q3W


@[expose] def ProductP1Input3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    RouteD3Setup K z → ∀ M ∈ conjClass3 K, ∀ w : G, IsClassicalMember3 M w → Commutes K M →
      z ≠ w → LocalOddCentral (conjClass3 K) {z * w} ∧
        LocalOddThreeFree3 (conjClass3 K) (z * w)

end CFSG.ClassicalInvolution.Q3.Q3TC
