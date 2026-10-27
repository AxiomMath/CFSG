module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWHyp
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEDefs

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

namespace TwinThmEW

section Quot



class PrintedQuotOdd : Prop where
  exists_W : ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G)
    (S : Sylow 2 G) (R W H : Subgroup G) (N : Subgroup G) [N.Normal],
    TwinThmE.EStandQ8 Ω K S R W → CentPairs Ω (S : Subgroup G) W H → Odd (Nat.card N) → N ≤ H →
      ∃ Wb ∈ WSet (quotFamily Ω N),
        Wb ≤ (S : Subgroup G).map (QuotientGroup.mk' N) ∧
        (∀ s ∈ (S : Subgroup G).map (QuotientGroup.mk' N), conjSub s Wb = Wb) ∧
        CentPairs (quotFamily Ω N) ((S : Subgroup G).map (QuotientGroup.mk' N)) Wb
          (H.map (QuotientGroup.mk' N))

end Quot

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
