module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWDefs

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

namespace TwinThmEW

section QuotCent


class PrintedQuotCent : Prop where
  exists_W : ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G)
    (S : Sylow 2 G) (R W H : Subgroup G) (N : Subgroup G) [N.Normal],
    MinCexQ8 Ω K S R W H → N ≤ Subgroup.center G → IsPGroup 2 ↥N → N ≤ H →
      (∀ J ∈ Ω, J ⊓ N = ⊥) →
      ∃ Wb ∈ WSet (quotFamily Ω N),
        Wb ≤ (S : Subgroup G).map (QuotientGroup.mk' N) ∧
        (∀ s ∈ (S : Subgroup G).map (QuotientGroup.mk' N), conjSub s Wb = Wb) ∧
        CentPairs (quotFamily Ω N) ((S : Subgroup G).map (QuotientGroup.mk' N)) Wb
          (H.map (QuotientGroup.mk' N))

end QuotCent

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
