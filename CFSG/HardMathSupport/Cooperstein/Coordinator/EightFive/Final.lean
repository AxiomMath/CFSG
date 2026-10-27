module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.StepAssembly
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base8
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ExitNine
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ExitTenEven
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ExitTenOdd
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ExitLargeNat
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ExitLargeExotic
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ExitSixteen

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

theorem gf2EightFive_of_b42L42Core (hB42 : B42L42Core) :
    GF2EightFive :=
  gf2EightFive_of_exits (tperm_eight_of hB42) exitNineFix exitTenEven exitTenOdd exitLargeNat
    exitLargeExotic exitSixteenTransitive

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
