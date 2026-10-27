module

public import CFSG.HardMathSupport.MathTwE6.MonsterThreeBDown
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.L3AutGen
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BM2Census

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.Sec6.BM2

open CFSG.HardMathSupport.MathTwE6.M3BIrr CFSG.HardMathSupport.Solomon.Coordinator.YS08

theorem l3AutDvd_holds : L3AutDvd := fun _ _ _ _ h => l3AutDvd_of_isL3Kind h

section Down


theorem sporL3DownInner_M_holds : SporL3DownInner .M :=
  sporL3DownInner_M_of_census_gmat l3AutDvd_holds
    (fun s hs hi => Or.inl (m3bClass_holds s hs hi))

end Down

end CFSG.HardMathSupport.Dickson.Sec6.BM2
