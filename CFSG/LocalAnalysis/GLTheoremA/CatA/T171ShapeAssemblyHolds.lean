module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcKernelSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcKernelCubeTransfer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcHighFixAll
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTwoDFourE8Main
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Prelim

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

theorem excKernelCompAction_holds : ExcKernelCompAction :=
  excKernelCompAction_of twoDExcFixedPointsPerfectAll_holds innerKindSmallCompAction_holds
    (excHighRankCompAction_of_fixedPerfect excHighRankFixedPerfectAll_holds
      excHighRankCubeTransfer_holds)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
