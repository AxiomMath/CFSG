module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResExcRee
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResExcTriThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResExcTwE6
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResTits
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResSpFamily
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResDiag
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTwoGroupAssembly
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBTits
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBG2Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcTwE6
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcF4
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcHolds
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.ExcWideThree.G2
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcWideThree

theorem almostSimplePartBRankTwo_holds
    : AlmostSimple.AlmostSimplePartBRankTwo :=
  AlmostSimple.almostSimplePartBRankTwo_of_inner_outer TwoSignalizer.signalizerTwoGroupKFact_holds
      (AlmostSimple.chevTwoOuterPElementIsLThree_of_leaves AlmostSimple.chevTwoOuterFixesPair_sp
          AlmostSimple.chevTwoOuterFixesPair_omegaPlus AlmostSimple.chevTwoOuterFixesPair_omegaMinus
          AlmostSimple.chevTwoOuterFixesPair_E6 AlmostSimple.chevTwoOuterFixesPair_twistedE6
          AlmostSimple.chevTwoOuterFixesPair_E7 AlmostSimple.chevTwoOuterFixesPair_E8
          AlmostSimple.chevTwoOuterFixesPair_F4
          (AlmostSimple.ChevTwoOuterFixesPair.of_three_geFive
              AlmostSimple.chevTwoOuterFixesPair_G2_three
              AlmostSimple.chevTwoOuterFixesPair_G2_geFive)
          (AlmostSimple.ChevTwoOuterFixesPair.of_three_geFive
              AlmostSimple.chevTwoOuterFixesPair_trialityD4_three
              AlmostSimple.chevTwoOuterFixesPair_trialityD4_geFive)
          AlmostSimple.chevTwoOuterFixesPair_suzuki AlmostSimple.chevTwoOuterFixesPair_reeF4
          AlmostSimple.chevTwoOuterFixesPair_tits)
      (AlmostSimple.chevTwoInnerTwoPartCentralizedRest_of_inputs
          AlmostSimple.chevTwoPClosureOddE6_holds AlmostSimple.chevTwoPClosureOddE7_holds
          AlmostSimple.chevTwoPClosureOddE8_holds AlmostSimple.chevTwoPClosureOddF4_holds
          AlmostSimple.chevTwoPClosureOddG2_holds AlmostSimple.chevTwoPClosureOddTwistedE6_holds
          AlmostSimple.chevTwoPClosureOddTrialityD4_holds AlmostSimple.chevTwoPClosureOddReeF4_holds
          AlmostSimple.chevTwoPClosureOddTits_holds)
      AlmostSimple.chevTwoDiagonalTwoPartCentralized_holds

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth
