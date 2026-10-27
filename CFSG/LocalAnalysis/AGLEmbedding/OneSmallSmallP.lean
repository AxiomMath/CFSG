module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPOdd
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPJ3

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D1SmallEvenA6U33 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → ∀ z : G, D1SmallCZElt p H R K z →
    p = 3 → (IsAltTwoP 3 K ∨ IsSmallUnitary 3 K) → D1CzB0 p R z → D1CzEven p z →
    D1CzIso p z K → D1SmallOpenPosIf p M H Rbar K → False

theorem d1SmallU33_of (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp)
    (hNo2 : KFactSmallNoTwo) (hShape : KFactSmallSylowShape) (hOrb : KFactSmallOrbits)
    (hO : KFactSmallThreeOrders) (hEv : D1SmallEvenA6U33) : D1SmallU33 := by
  intro G _ _ p P M H R Rbar K hd huniq z hz hp3 hU hB0 hIso hOP
  by_cases hE : D1CzEven p z
  · exact hEv G p P M H R Rbar K hd huniq z hz hp3 (Or.inr hU) hB0 hE hIso hOP
  · exact hd.false_of_b0_odd hOut hExp hNo2 hShape hOrb hz hB0 hE hIso
      (fun h => by omega) (fun _ hL => absurd hL (not_l34_and_not_a6_of_u33 hO hU).1)

theorem d1SmallA6_of (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp)
    (hNo2 : KFactSmallNoTwo) (hShape : KFactSmallSylowShape) (hOrb : KFactSmallOrbits)
    (hO : KFactSmallThreeOrders) (hSch : KFactCatalogSchreier) (hJ3c : KFactJ3CoverA6)
    (hEv : D1SmallEvenA6U33) : D1SmallA6 := by
  intro G _ _ p P M H R Rbar K hd huniq z hz hp3 hA h
  rcases h with ⟨hB0, hIso, -, hOP⟩ | ⟨hSP, hJ3⟩
  · by_cases hE : D1CzEven p z
    · exact hEv G p P M H R Rbar K hd huniq z hz hp3 (Or.inl hA) hB0 hE hIso hOP
    · exact hd.false_of_b0_odd hOut hExp hNo2 hShape hOrb hz hB0 hE hIso
        (fun h => by omega) (fun _ hL => absurd hL (not_l34_of_a6 hO hA))
  · exact d1SmallA6J3_of hSch hJ3c G p P M H R Rbar K hd huniq z hz hp3 hA hSP hJ3

end CFSG.AGLEmbedding
