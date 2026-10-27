module

public import CFSG.LocalAnalysis.OddStandard.L2Ree.L2Half
public import CFSG.LocalAnalysis.OddStandard.L2Ree.TheoremOneLeaves
public import CFSG.LocalAnalysis.OddStandard.SporadicRow.AnyMain
public import CFSG.RankThree.PartTwo.Sec4.Census.WiringInputs
public import CFSG.LocalAnalysis.SeitzReduction.GLS3OddHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenOuter

public section

namespace CFSG.OddStandard.L2Ree

open CFSG CFSG.ComponentClassification

section Certified

open _root_.Certificates


theorem l2Half_of_milestones
    (hGH : UFrontier.GH74ModelsInput) (hCI : GSLit.ClassicalInvolutionInput) : L2Half :=
  l2_half_of_arms TBLit.griessMultipliersOdd_holds
    RankThree.PartTwo.Sec4.Census.griessMultipliersCentralCovers
    (theoremOne_of_leaves hGH hCI) SeitzReduction.gls3OddLieAutComponentsInput
    (fun _ _ h => CatLeaf.involutionCentralizersComponentFree_of_evenLieType h)
    CatLeafProof.evenLieOuterTwoComponentsInput_holds
    (fun s hs => HarrisLit.T1.SporRow.sporOddCompsAny_of s hs)

end Certified

end CFSG.OddStandard.L2Ree
