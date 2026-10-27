module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeD4ThreeAdj
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeD4ThreeTw
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeD4ThreeG2Two
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeD4ThreeSetup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171D4

open CFSG.LocalAnalysis.GLTheoremA.T171Sh

set_option linter.unusedSectionVars false

theorem excAdjD4Inner_holds : F151.ExcAdjD4Inner :=
  excAdjD4Inner_of_G2Two d4ExitAt_adjoint_G2_two

theorem smallExitD4AtThree_untw_holds :
    SmallExitD4AtThree fun i : TauCeti.LieTypeIndex =>
      KD264Lie.isExcUntwistedIdx i ∧ i.characteristic = 2 :=
  smallExitD4AtThree_untw_of excAdjD4Inner_holds

theorem smallExitD4AtThree_twE6_holds :
    SmallExitD4AtThree fun i : TauCeti.LieTypeIndex =>
      (∃ q : TauCeti.PrimePower, i = .twistedE6 q) ∧ i.characteristic = 2 :=
  smallExitD4AtThree_twE6_of twE6D4Inner_holds

end CFSG.LocalAnalysis.GLTheoremA.T171D4

end
