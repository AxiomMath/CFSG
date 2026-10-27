module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShNorm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShNormCat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShNormL3
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.ScopeBInputs
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Final
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TCAll
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6Holds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6Ident
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6D4T2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6Final
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShLowerTwE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShFixU3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6KernelExitWire
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcInnerD4FixMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeAssemblyHolds
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.E6BadLift
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Comp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151DiagDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeD4ThreeHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6KernelExitFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcAdj
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamChar2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInBCDCharTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamTriAct
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamTriLang
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamTriMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeLinStatedInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeReeF4LargeRFHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwE6CompAct
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwE6Conn
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeUniInner
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93IdNot2
public import CFSG.Quasithin.Background.B3ThreeModel
public import CFSG.Quasithin.Background.B3ThreeStruct
public import CFSG.Quasithin.Background.G2Omega4PlusModule
public import CFSG.Quasithin.Background.SmithB42L2L32
public import CFSG.Quasithin.Background.SmithB42L2Nat
public import CFSG.Quasithin.Background.SmithB51LnRealB
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompO
public import CFSG.Quasithin.EmptyFaithful.R3c19B
public import CFSG.Quasithin.EmptyFaithful.S143FF
public import CFSG.Quasithin.EmptyFaithful.S143Final
public import CFSG.Quasithin.EmptyFaithful.S143HD
public import CFSG.Quasithin.EmptyFaithful.S143IG
public import CFSG.Quasithin.EmptyFaithful.S143JB
public import CFSG.Quasithin.EmptyFaithful.S143KO
public import CFSG.Quasithin.EmptyFaithful.S143KP
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15421
public import CFSG.RankThree.PartOne.N143.HighEvenU

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

theorem t158ShapeLieOn_E6_of_kernel
    (hK : T171Sh.ExcKernelCompAction)
    (hI : E6D4T2InnerCosetAction) : T158ShapeLieOn t158ShapeE6 :=
  t158ShapeLieOn_E6
    (t158Norm_of_tables CFSG.HardMathSupport.Timmesfeld.Coordinator.tables112_holds
      CFSG.HardMathSupport.Timmesfeld.Tables.Census.tableL2_unconditional
      CFSG.HardMathSupport.Solomon.Coordinator.tables112Types_holds t158NormCat_holds
      t158NormL3_holds)
    (t158SetupE6_of_kernel_inner hK hI)
    (T171Sh.KExit.e6Bound_of_kernel hK T171Sh.innerD4FixedPointsPerfect_holds false)

theorem t158ShapeLieOn_TwE6_of_kernel
    (hK : T171Sh.ExcKernelCompAction)
    (hI : E6D4T2InnerCosetAction) : T158ShapeLieOn t158ShapeTwE6 :=
  t158ShapeLieOn_TwE6
    (t158Norm_of_tables CFSG.HardMathSupport.Timmesfeld.Coordinator.tables112_holds
      CFSG.HardMathSupport.Timmesfeld.Tables.Census.tableL2_unconditional
      CFSG.HardMathSupport.Solomon.Coordinator.tables112Types_holds t158NormCat_holds
      t158NormL3_holds)
    (t158SetupE6_of_kernel_inner hK hI)
    (T171Sh.KExit.e6Bound_of_kernel hK T171Sh.innerD4FixedPointsPerfect_holds true)
    lowerTwE6_holds (t158IdentTwE6Pre_of hK (e6D4T2CosetAction_of_inner hI)) t158FixU3_holds

end CFSG.LocalAnalysis.GLTheoremA.T158

end
