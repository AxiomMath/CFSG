module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnD4c
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnD4b

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.LocalBalance

set_option linter.unusedSectionVars false


theorem u4InnAt_d4two : U4InnAt S9.isD4two := by
  intro S _ _ hcat hS u hu3 hq
  by_cases hin : u ∈ innerAut S
  · obtain ⟨g, rfl⟩ := hin
    exact u4InnInner_d4two hcat hS g hu3 hq
  · exact (u4InnOuter_d4two hcat hu3 (fun a ha => hin ⟨a, ha⟩) hq).elim

end CFSG.LocalAnalysis.GLTheoremA.CatB

end
