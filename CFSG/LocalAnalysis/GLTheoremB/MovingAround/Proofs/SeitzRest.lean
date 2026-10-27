module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256e2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311f2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256d2
public import CFSG.LieType.SeitzGeneration.QuasiHigh4
public import CFSG.LieType.SeitzGeneration.QuasiHigh5Rest

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzRest

@[expose] def Input25_6A5Rest4 : Prop :=
  Inputs256d.Chev2BigRest ∧ Inputs256c.Chev2GF4 ∧ Inputs256d.Chev2GF2Rest

@[expose] def SeitzLowRest3 : Prop :=
  CFSG.LieType.SeitzGeneration.QuasiHigh5.SeitzCoverFamExcRest2Rest ∧
    CFSG.LieType.SeitzGeneration.QuasiHigh4.SeitzCoverCubeRest4 ∧
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2310CubeSimple

@[expose] def SeitzThm4Rest3 :
    Prop :=
  Inputs2311c.UniSeitzPlanes Inputs2311f.OddCpfRest3 ∧ Inputs256e.QGenSympOrth ∧ Inputs256e.QGenExc ∧
    Inputs256e.Input14_2StructThree

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzRest

end
