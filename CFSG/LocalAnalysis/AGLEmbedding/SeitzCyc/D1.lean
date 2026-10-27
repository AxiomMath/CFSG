module

public import CFSG.LocalAnalysis.AGLEmbedding.SeitzCyc.ExcCyc
public import CFSG.LieType.SeitzGeneration.RootPairOrthPlusChar2
public import CFSG.LieType.SeitzGeneration.RootPairOrthMinusChar2
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicOuter
public import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLieCharRankProof
public import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinThreeOut
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.LieType.SeitzGeneration.SeitzFrontier
public import CFSG.LieType.SeitzGeneration.SubfieldPairSLLtProof
public import CFSG.LieType.SeitzGeneration.SpF2.Main
public import CFSG.HardMathSupport.Malle.Coordinator.SubfieldPairs.SUOddTwoBig
public import CFSG.LieType.SeitzGeneration.UnitaryHeisCoreMain
public import CFSG.LieType.SeitzGeneration.OuterCoreProof
public import CFSG.LieType.SeitzGeneration.OuterSmallCases
public import CFSG.LieType.SeitzGeneration.OuterOrth
public import CFSG.LieType.SeitzGeneration.RootPairOrthOmega

public section

namespace CFSG.AGLEmbedding.SeitzCyc

open CFSG.Open CFSG.AGLEmbeddingD2 CFSG.LieType.SeitzGeneration


theorem kFactSeitzCyc_of_pairs_cyc (hOP : SubfieldPairOmegaPlusF2)
    (hOM : SubfieldPairOmegaMinusF2) (hXC : SeitzExcOuterCycResiduals) : KFactSeitzCyc :=
  kFactSeitzCyc_of_inputsCyc kFactLieCharRank kFactLieCharOut
    (not_dvd_card_outer_sporadic CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group)
    (seitzOuterCyc_of (seitzOuterLowNarrow_of_pairs' subfieldPairSLLt
      (subfieldPairSpOdd subfieldPairSpF2_holds)
      (subfieldPairSUOdd
        CFSG.HardMathSupport.Malle.Coordinator.SubfieldPairs.subfieldPairSUOddTwo_holds)
      unitaryHeisCore (unitaryOuterHeisCore_of_finite_cases HeisSmall.outerB12AtCard_five
          HeisSmall.outerB12AtCard_eight HeisSmall.outerB12AtCard_eleven)
      (seitzOuter_orthogonal_narrow (subfieldPairOmega_of_char2
        (subfieldPairOmegaPlusChar2_of_F2 hOP) (subfieldPairOmegaMinusChar2_of_F2 hOM)))) hXC)

end CFSG.AGLEmbedding.SeitzCyc
