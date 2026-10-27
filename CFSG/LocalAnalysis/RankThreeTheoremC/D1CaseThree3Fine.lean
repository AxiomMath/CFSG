module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3A9
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Chev
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3FineKFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3ReeF4
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3J3
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3LinTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp48Rank7
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp62Close
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

theorem D1CaseThreeFineResidues3.of_kfacts (hk : D1CaseThreeFineKFacts3) :
    D1CaseThreeFineResidues3 G :=
  have hB3 : StmtBlockThree :=
    stmtBlockThree_of hk.eightFive hk.eightSix hk.nineThree hk.noXBlock hk.parabolicThree
      hk.citedBlockThree hk.blockThreeAltSeven
  { a9 := d1CaseThreeA9At3_closed hk.a9Local hk.jStarElimA3p hk.blockThreeOneOrbit hk.beta
      hk.p1Lie hk.p1Alt hk.p1Spor hk.eightFour hk.eightFive hk.eightSix hk.nineThree
      hk.noXBlock hk.parabolicThree hk.citedBlockThree hk.blockThreeAltSeven hk.localCGT
    j3 := d1CaseThreeJ33_closed hk.j3Sylow hk.j3OuterInvolution hk.j3OuterRank hk.j3Target
      hk.j3TargetCard hk.jStarElimJ3 hk.blockThreeSolvable hk.beta hk.p1Lie hk.p1Alt hk.p1Spor
      hk.eightFour hk.eightFive hk.eightSix hk.nineThree hk.noXBlock hk.parabolicThree
      hk.citedBlockThree hk.blockThreeAltSeven hk.localCGT
    linTwo := fun p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d hd e =>
      d1CaseThreeLinTwoAt3_closed hk.beta hk.p1Lie hk.p1Alt hk.p1Spor hk.jStarElimLie
        hk.jStarElimAlt hk.jStarElimSpor hk.localCGT hk.noXBlock hk.eightFour hk.eightFive
        hk.eightSix hk.nineThree hk.parabolicThree hk.citedBlockThree hk.blockThreeAltSeven
        hk.lemmaB hk.threeOrFiveDvd hk.outElemRank p P M H R Rbar hcfg K hK huniq hnc hcent hKD d
        ⟨3, hd⟩ e
    survivors :=
      { sp62 := d1CaseThreeSp62At3_closed hk.survivorSchur hk.sp62Local hk.eightFour hk.eightFive
          hk.eightSix hk.nineThree hk.noXBlock hB3 stmtBlockInnerNormalizer_of hk.blockLeviU42
          (d1Sp62BlockResidue3_of_sylow hk.survivorSchur hk.sp62Local hk.eightFour hk.noXBlock
            hk.omegaEightMinusAut hk.u62ThreeRank hk.omegaMinusThreeRank
            (d1Sp62Omega8SylowResidue3_closed hk.gl83 hk.survivorSchur hk.sp62Frame
              hk.omega8Frame))
        sp48 := d1CaseThreeSp48At3_closed hk.survivorSchur hk.sp48Local hk.sp48Data hk.sp48Target
          hk.jStarElimSp48 hk.beta hk.p1Lie hk.p1Alt hk.p1Spor hk.eightFour hk.eightFive
          hk.eightSix hk.nineThree hk.noXBlock hB3 stmtBlockInnerNormalizer_of hk.blockThreeOut
          hk.blockThreeOrderNine hk.localCGT
          (d1Sp48NonsolvResidue3_closed hk.survivorSchur hk.sp48Local hk.sp48NonsolvLocal
            hk.eightFour hk.eightFive hk.nineThree hk.noXBlock hB3 hk.blockL28Transvection
            hk.blockL28Rank hk.blockL28TwoRank)
        reeF4 := d1CaseThreeReeF4At3_closed hk.survivorSchur hk.reeF4Local hk.reeF4Target
          hk.jStarElimReeF4 hk.blockFiveParabolic hk.outFiveCyclic hk.beta hk.p1Lie hk.p1Alt
          hk.p1Spor hk.eightFour hk.eightFive hk.eightSix hk.nineThree hB3
          stmtBlockInnerNormalizer_of hk.threeOrFiveDvd hk.localCGT hk.noXBlock } }

end CFSG.LocalAnalysis.RankThreeTheoremC
