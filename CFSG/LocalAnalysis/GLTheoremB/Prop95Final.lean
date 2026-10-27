module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95Frontier
public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvMain
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1920Final
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1921Final
public import CFSG.LocalAnalysis.GLTheoremB.I2810.Main
public import CFSG.LieType.ChevTwo.Main
public import CFSG.LieType.ChevTwo.Orthogonal
public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvFactSixSeven
public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvFactAltChevMain
public import CFSG.LieType.ChevTwo.InversionBase

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts

open CFSG.LieType.ChevTwo CFSG.LocalAnalysis.GLTheoremB.Prop95Iv


theorem prop95_holds : Prop95 :=
  have hKD : Chev2KDOut := chev2KDOut_of_outTwoNilp chev2OutTwoNilp_of_leaves
  have hCore : Chev2CoreCent := chev2CoreCent_of_leaves
  have h2810 : Input28_10 := I2810.input28_10_of_leaves
    (chev2OutTwoRank_of_leaves fun _ _ _ h =>
      CFSG.HardMathSupport.Cooperstein.StructureLie.outTwoRank_of_isClassicalTwoOrG2 h)
    chev2RankTwoInverts omegaTwoAutTwoPart
  have hiv := prop95Iv_of lemma96_holds (input19_20_2_of_catalogue hKD hCore)
    (input19_20_3_of_leaves hKD hCore omegaTwoAutTwoPart omegaTwoAutInduced
      omegaPlusEightInvolutions orthOddCentCore)
    Prop95I1921.input19_21_1_proof Prop95I1921.input19_21_2_proof h2810
    omegaCentreTrivial_holds altNotChevTwo_holds hatSevenOddInverts_holds altSixSevenCentre_holds
    a7Facts_holds
  prop95_of_iv hiv.1 hiv.2

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
