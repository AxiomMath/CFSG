module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Main
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Dispatch
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Even
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42SporAll
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4YElem
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4Gomi

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

theorem gomiU42Input_of_selector
    (hGA : CFSG.Open.GriessAllModelsStatement) (hS : GomiU42Selector fun _ _ => True) :
    GomiU42Input := by
  intro G _ _ d h
  exact h.gomiU42_of_selector hGA hS (fun y hy => h.Y_sq hy)

theorem gomiU42Input_of_oddLie
    (hOdd : GomiU42Selector fun D _ => CFSG.Blueprint.OddLieType D) :
    GomiU42Input :=
  gomiU42Input_of_selector CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    (gomiU42Selector_of_families gomiU42Selector_alternating hOdd gomiU42Selector_even
      gomiU42Selector_sporadic)

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
