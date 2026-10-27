module

public import CFSG.ClassicalInvolution.Asc77.AscT3UMain
public import CFSG.ClassicalInvolution.Asc77.AscT3VFinal

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII.T3V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime]


theorem c20_10b_proved : C20_10b p f :=
  c20_10b_of_P1 p f (res10bP1_proved p f)

theorem t3CaseII_of_res10aY (hY : Res10aY p f) : T3CaseII p f :=
  T3U.t3CaseII_of_res10 (res10bP1_proved p f) hY

variable (p f) in
@[expose] def Res10aYNe9 : Prop := p ^ f ≠ 9 → Res10aY p f

variable (p f) in
@[expose] def Res10aY9 : Prop := p ^ f = 9 → Res10aY p f

theorem res10aY_of_cases (h1 : Res10aYNe9 p f) (h2 : Res10aY9 p f) : Res10aY p f := by
  by_cases h : p ^ f = 9
  · exact h2 h
  · exact h1 h

theorem t3CaseII_of_cases (h1 : Res10aYNe9 p f) (h2 : Res10aY9 p f) : T3CaseII p f :=
  t3CaseII_of_res10aY (res10aY_of_cases h1 h2)

end CFSG.ClassicalInvolution.Asc77.T3CII.T3V
