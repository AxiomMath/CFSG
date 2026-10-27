module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcKernelSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcKernelCubeTransfer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcHighFixAll
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamChar2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeLinStatedInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeUniInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeUniBlockHoldsMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInBCDCharTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamTriMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamTriLang
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamTriAct
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcAdj
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcSmallD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwE6CompAct
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwE6Conn
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeReeF4LargeRFHolds
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Prelim

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

theorem excKernelCompAction_of_perfectAll (hP : TwoDExcFixedPointsPerfectAll) :
    ExcKernelCompAction :=
  excKernelCompAction_of hP innerKindSmallCompAction_holds
    (excHighRankCompAction_of_fixedPerfect excHighRankFixedPerfectAll_holds
      excHighRankCubeTransfer_holds)

theorem shape15On_charTwo_of_inputs (hP : TwoDExcFixedPointsPerfectAll)
    (h3 : SmallExitD4AtThree fun i : TauCeti.LieTypeIndex =>
      CFSG.LocalAnalysis.GLTheoremA.KD264Lie.isExcUntwistedIdx i ∧ i.characteristic = 2)
    (h3Tw : SmallExitD4AtThree fun i : TauCeti.LieTypeIndex =>
      (∃ q : TauCeti.PrimePower, i = .twistedE6 q) ∧ i.characteristic = 2) :
    Shape15On fun _ => True :=
  shape15On_of_charTwo
    innerCompNonShape_linear_charTwo
    (innerCompNonShape_unitary_charTwo_of_block uniBlockInnDiag_holds)
    innerCompNonShape_classicalBCD_charTwo_holds
    (innerCompNonShape_triality_charTwo_of triCompClassical_holds triCompAction_holds)
    (innerCompNonShape_excUntwisted_charTwo_of
      (excAdjCompInnAut_of (excKernelCompAction_of_perfectAll hP)
        e6CentralizerConnOddExcKernels_holds)
      (excSmallExit_of (excSmallExitD4_of_three h3)))
    (innerCompNonShape_excTwisted_charTwo_of
      (innerCompNonShape_twistedE6_charTwo_of (excKernelCompAction_of_perfectAll hP)
        twE6CentralizerConnOdd_holds (twE6SmallExit_of (twE6SmallExitD4_of_three h3Tw))
        twE6ComponentAction_holds)
      reeF4CompInner_holds)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
