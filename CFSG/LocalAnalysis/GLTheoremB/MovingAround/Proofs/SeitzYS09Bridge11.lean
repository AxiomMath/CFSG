module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV49
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzYS09Bridge10
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzRest5Even

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge11

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false


@[expose] def SeitzLowRest15 : Prop :=
  CubeCoverE6.CoverE6DiagNotAll24 ∧ CubeCoverE6.CoverTwE6Cubes ∧ ChevQ.SeitzExcOpenResidual15 ∧
    ChevQ.E6Three.KSGen.TwE6ConnFixed 40

theorem seitzLowRest14_of_rest15 (h : SeitzLowRest15) : SeitzYS09Bridge10.SeitzLowRest14 :=
  ⟨SeitzRest5.twE6ThreeOpenDiagEven_holds, h.1, h.2.1,
    ⟨h.2.2.1.1, h.2.2.1.2.1, h.2.2.1.2.2.1,
      ChevQ.E6ThreeInner.twE6ToralNegTwo_of_regularLangNeg ChevQ.E6ThreeInner.twE6RegularLangNeg_of_cert,
      ChevQ.E6ThreeInner.twE6InnerA2CaseTwo_of_frameH0 ChevQ.E6ThreeInner.twE6SylowMonoTwoAt_holds
        h.2.2.1.2.2.2.1,
      ChevQ.E6ThreeInner.twE6InnerNoA2Two_of_cycNonA2_rankTwo h.2.2.1.2.2.2.2.1 h.2.2.1.2.2.2.2.2.1,
      h.2.2.1.2.2.2.2.2.2.1, h.2.2.1.2.2.2.2.2.2.2⟩,
    h.2.2.2⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge11

end
