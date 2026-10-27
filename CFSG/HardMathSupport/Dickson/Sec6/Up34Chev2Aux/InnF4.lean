module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcFam
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcChar2
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDF4
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSuN

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Dickson.Sec6.Up34Exc

namespace Up34Chev2

section F4

set_option linter.unusedSectionVars false


theorem up34C2Inn_F4_holds : Up34Chev2Inn FamF4 := by
  have h24 : ∀ (L : Type) [Field L] [CharP L 2] (a : Fin Tag.F4.rank → Lˣ), (∀ j, a j ^ 3 = 1) →
      ∀ i : KernelComponent (rootCharHom a), (componentRoots (rootCharHom a) i).ncard ≠ 24 := by
    intro L _ _ a ha i h
    rcases rdValues_F4 L a ha i with h' | h' | h' <;> omega
  have hr : Tag.F4.rank ≤ 4 := by decide
  exact up34C2Inn_F4_of_kinds (char2Hrat_inner (Or.inl rfl) rdSize_F4 rdGlue_F4)
    (char2Hrat_suN (Or.inl rfl) rdSize_F4) (char2Hrat_twoD_of_no24 hr h24)
    (char2Hrat_exc_of_no24 hr h24)

end F4

end Up34Chev2

end CFSG.HardMathSupport.Dickson.Sec6
