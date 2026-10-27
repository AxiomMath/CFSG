module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarSecEight
public import CFSG.LocalAnalysis.SeitzReduction.GLS3OddHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltOpen
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltEvenCenter
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveM12NotTop
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveCaseI
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenSmall
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltThree
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenFive
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbFinal

public section

namespace CFSG.OddStandard.AltStdSec


theorem shapeTwoCentDoubleAt_twelve_holds : ShapeTwoCentDoubleAt 12 :=
  shapeTwoCentDoubleAt_twelve CFSG.SeitzReduction.gls3OddLieAutComponentsInput
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
    (ComponentClassification.RankTwoAlt.rankTwoAlternatingStandard_of_open
        (ComponentClassification.RankTwoAltFive.altFiveCaseI_of
            (ComponentClassification.RankTwoAlt.altGenerationFive_of
                ComponentClassification.AS76b.asc08Lemma34
                ComponentClassification.Asc76X.goldschmidtTheoremA))
        (ComponentClassification.RankTwoAltFive.asc310EpsOne_of
            ComponentClassification.Asc76X.goldschmidtTheoremA)
        ComponentClassification.RankTwoAltFive.asc310IIb
        ComponentClassification.RankTwoAlt.altFiveM12NotTop_of
        ComponentClassification.RankTwoAlt.altEvenCenterSmall
        ComponentClassification.RankTwoAlt.altThreeCover
        (ComponentClassification.RankTwoAlt.altGenerationSmall_of
            ComponentClassification.AS76b.asc08Lemma34
            ComponentClassification.Asc76X.goldschmidtTheoremA)
        ComponentClassification.RankTwoAlt.altRootFusion
        (ComponentClassification.RankTwoAlt.altTypeTwoFusion_of_rootFusion
            ComponentClassification.RankTwoAlt.altRootFusion)
        (ComponentClassification.RankTwoAlt.altTypeTwoCentralizer
            ComponentClassification.Asc76X.goldschmidtTheoremA))

end CFSG.OddStandard.AltStdSec
