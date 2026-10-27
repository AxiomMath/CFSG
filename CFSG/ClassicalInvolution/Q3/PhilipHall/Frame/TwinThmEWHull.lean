module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf8Core
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWDefs

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

namespace TwinThmEW

section Hull



class PrintedHull : Prop where
  exists_W : ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G)
    (S : Sylow 2 G) (R W H : Subgroup G) (w : G),
    MinCexQ8 Ω K S R W H → w ≠ 1 → w * w = 1 →
    ∀ S₁ : Sylow 2 ↥(coreHull Ω w), R ≤ (S₁ : Subgroup ↥(coreHull Ω w)).map (TwinThmE.secEmb Ω w) →
      ∃ W₁ ∈ WSet (hullFam Ω w), W₁ ≤ (S₁ : Subgroup ↥(coreHull Ω w)) ∧
        (∀ s ∈ (S₁ : Subgroup ↥(coreHull Ω w)), conjSub s W₁ = W₁) ∧
        CentPairs (hullFam Ω w) (S₁ : Subgroup ↥(coreHull Ω w)) W₁ (H.comap (TwinThmE.secEmb Ω w))

end Hull

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
