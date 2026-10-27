module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.AutRankThree.GLThreeOf
public import CFSG.RankThree.PartOne.KF.BloomClose
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusL2

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

theorem glIrrQuasisimpleThreeDvd_holds :
    GLIrrQuasisimpleThreeDvd :=
  glIrrQuasisimpleThreeDvd_of CFSG.RankThree.PartOne.extBloomMitchell_holds fun p _ H h3 =>
    CFSG.RankThree.PartTwo.Sec6.BThreeCensus.isSolvable_of_not_three_dvd_psl2 (f := 1)
      (by rw [Nat.card_zmod, pow_one]) H h3

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
