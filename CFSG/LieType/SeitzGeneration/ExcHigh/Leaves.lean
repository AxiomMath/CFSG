module

public import CFSG.LieType.SeitzGeneration.ExcHigh.CubeClasses
public import CFSG.LieType.SeitzGeneration.ExcHigh.F4One
public import CFSG.LieType.SeitzGeneration.ExcHigh.F4Two
public import CFSG.LieType.SeitzGeneration.ExcHigh.E7Seven
public import CFSG.LieType.SeitzGeneration.ExcHigh.E7Low
public import CFSG.LieType.SeitzGeneration.ExcHigh.E7TwoLowEven
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8One
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8TwoLow
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8Four
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6One
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJPlacement
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Phi6RouteWStarProved
public import CFSG.ClassicalInvolution.RouteD.GapsOrthChain
public import CFSG.ClassicalInvolution.RouteD.MultiModelGlue
public import CFSG.ClassicalInvolution.RouteD.MultiStarStd
public import CFSG.HardMathSupport.Lang.AnisoE8.D8Planes
public import CFSG.HardMathSupport.Lang.AnisoF4.B4PlanesEven
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.Quasithin.Background.G11Stmts
public import CFSG.RankThree.PartOne.KE.E6FourPlane
public import CFSG.RankThree.PartOne.KE.E7FourPlane
public import CFSG.RankThree.PartOne.KE.E7ThreeFinal
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open TauCeti

 

theorem seitzExcHighTwE6Six_proved : SeitzExcHighTwE6Six := by
  exact seitzExcHighTwE6Six_of_phi6 fun r hr =>
    CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.phiPlaneGenAt_neg_of_coreW hr
      (CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.phi6CoreW_of_placementSome hr
        (CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.phi6PlacementSome_holds r hr)
        (CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.phi6PlacementSomeThree_holds r hr))

@[expose] def SeitzExcHighE8OneLtSeven : Prop :=
  SeitzExcHighForAt IsE8Index fun d p => p < 7 ∧ ClassRange LieTypeIndex.E8 (fun _ => True) 1 d p

theorem seitzExcHighE8One_of_lt_seven (h : SeitzExcHighE8OneLtSeven) : SeitzExcHighE8One :=
  SeitzExcHighForAt.union (fun d p _ _ hQ => (Nat.lt_or_ge p 7).elim
    (fun h' => Or.inr ⟨h', hQ⟩) (fun h' => Or.inl ⟨hQ, h'⟩))
    seitzExcHighE8One_of_ge_seven h

theorem seitzExcHighTop_geFive_of_leaves (h72 : SeitzExcHighE7TwoSeven)
    (h81 : SeitzExcHighE8OneLtSeven) (h82 : SeitzExcHighE8TwoFive) (h83 : SeitzExcHighE8Three)
    (h84 : SeitzExcHighE8FourLtSeven) (h86 : SeitzExcHighE8Six) (h22 : SeitzExcHighTwE6Two) :
    SeitzExcHighForAt IsTopIndex PrimeRange.geFive := by
  exact SeitzExcHighForAt.top_of_families seitzExcHighF4_geFive seitzExcHighE6_geFive_proved
    (seitzExcHighE7_geFive_of_classes seitzExcHighE7One (seitzExcHighE7Two_of_seven h72)
      seitzExcHighE7Three seitzExcHighE7Six_proved)
    (seitzExcHighE8_geFive_of_classes (seitzExcHighE8One_of_lt_seven h81)
      (seitzExcHighE8Two_of_five h82) h83 (seitzExcHighE8Four_of_ge_seven_of_lt h84) h86)
    (seitzExcHighTwE6_geFive_of_classes seitzExcHighTwE6One h22 seitzExcHighTwE6Six_proved)

end CFSG.LieType.SeitzGeneration.ExcHigh
