module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.NineTwo
public import CFSG.HardMathSupport.Cooperstein.StructureLie.OpenFrontier
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TripleA7
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightTenNaturalOnlyOfResidual
public import CFSG.LocalAnalysis.AGLEmbedding.AscEightFive
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.Unconditional
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightTenLarge
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.B
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co1Final
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2Model
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co3
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Fi22Three
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Fi24Prime
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.HN
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.J3
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.M
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Ly
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.McL
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Suz
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.ON
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Th
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Final
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenMatchingFalse
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightTenSFourFalse
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base8Smith
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.Exceptional

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator

theorem asc81bNineThreeNat_of_nodes
    (hSm : Meierfrankenfeld.LieOdd.GF2NoFFLieOddSmall)
    (hERest : CoopersteinNoFFExceptionalRestNoE8) (hnp : StructureLie.EightNineNonParabolic)
    (hFO : AlternatingGeometry.EightTenNodeFourOrbit)
    (hCF : AlternatingGeometry.EightTenNodeColourFour) :
    CFSG.RankThree.PartTwo.Sec19.Asc81bNineThreeNat :=
  have h85 : GF2EightFive := EightFive.gf2EightFive_of_b42L42Core EightFive.b42L42Core_holds
  StructureLie.asc81bNineThreeNat_of_parts_noAlt
    (asc81bNineTwo_of (ffModuleTheorem_of (FFSporadic.gf2NoFFSporadic_of_each
      FFSporadic.gf2NoFFSporadicFor_J3 FFSporadic.gf2NoFFSporadicFor_Co1
      FFSporadic.gf2NoFFSporadicFor_Co2
      FFSporadic.gf2NoFFSporadicFor_Co3 FFSporadic.gf2NoFFSporadicFor_Fi22
      FFSporadic.gf2NoFFSporadicFor_Fi23 FFSporadic.gf2NoFFSporadicFor_Fi24Prime
      FFSporadic.gf2NoFFSporadicFor_McL FFSporadic.gf2NoFFSporadicFor_Suz
      FFSporadic.gf2NoFFSporadicFor_ONan FFSporadic.gf2NoFFSporadicFor_HN
      FFSporadic.gf2NoFFSporadicFor_Ly
      FFSporadic.gf2NoFFSporadicFor_Th FFSporadic.gf2NoFFSporadicFor_B
      FFSporadic.gf2NoFFSporadicFor_M)
      (Meierfrankenfeld.LieOdd.gf2NoFFLieOdd_of_small hSm)
      (coopersteinNoFFExceptional_of_rest (coopersteinNoFFExceptionalRest_of_noE8 hERest))))
    (StructureLie.chevNoAlt_of_nonParabolic hnp)
    (AlternatingGeometry.asc81bNineThreeAlt_of_eightTen
      (asc81bEightTen_of_printed_large
        (RichardWeiss.RecognitionPresentation.EightTenFour.asc81bEightTenPrinted_of_natural h85
          gf2NoFFTripleA7
          (eightTenNaturalOnly_of_residual (gf2NaturalLSL_of h85 gf2NoFFTripleA7)
            (AlternatingGeometry.eightTenResidualOutcomes_of_nodes eightTenNodeSFour hFO hCF
              AlternatingGeometry.eightTenNodeMatching))
          (CFSG.AGLEmbedding.asc81bEightFive_of_factorization
            CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved))
        Proving.quadFourExcluded_proved
        (eightTwoFourExcludedLarge_of Proving.eightTwoExcluded_proved
          (gf2NaturalLSL_of h85 gf2NoFFTripleA7))))

theorem asc81bNineThree_of_nodes
    (hSm : Meierfrankenfeld.LieOdd.GF2NoFFLieOddSmall)
    (hERest : CoopersteinNoFFExceptionalRestNoE8) (hnp : StructureLie.EightNineNonParabolic)
    (hFO : AlternatingGeometry.EightTenNodeFourOrbit)
    (hCF : AlternatingGeometry.EightTenNodeColourFour) :
    CFSG.AGLEmbedding.Asc81bNineThree :=
  CFSG.RankThree.PartTwo.Sec19.asc81bNineThree_of_nat
    (asc81bNineThreeNat_of_nodes
      hSm hERest hnp hFO hCF)

end CFSG.HardMathSupport.Cooperstein.Coordinator
