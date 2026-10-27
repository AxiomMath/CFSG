module

public import CFSG.ClassicalInvolution.Asc77.AscT3WFinal

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII.T3W

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable (p f : ℕ) [Fact p.Prime]


@[expose] def Res10aY'Ne9 : Prop := p ^ f ≠ 9 → Res10aY' p f

@[expose] def Res10aY'Nine : Prop := p ^ f = 9 → Res10aY' p f

variable {p f}

theorem res10aY'_of_cases (h1 : Res10aY'Ne9 p f) (h2 : Res10aY'Nine p f) : Res10aY' p f := by
  by_cases h : p ^ f = 9
  · exact h2 h
  · exact h1 h


theorem t3CaseII_of_cases' (h1 : Res10aY'Ne9 p f) (h2 : Res10aY'Nine p f) : T3CaseII p f :=
  t3CaseII_of_res10aY' (res10aY'_of_cases h1 h2)

end CFSG.ClassicalInvolution.Asc77.T3CII.T3W
