module

public import CFSG.GH74.E2.Cl2Enum
public import CFSG.GH74.E2.Cl2CaseA
public import CFSG.GH74.E2.Cl2CaseB
public import CFSG.GH74.E2.Cl2CaseC
public import CFSG.GH74.E2.Cl2CaseD

public section

namespace CFSG.GH74.E2

variable {Q : Type*} [Group Q] [Finite Q] {a b : MulAut Q} {N : Subgroup Q}

theorem Cl3.false (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) : False := by
  obtain ⟨a', b', h', hc⟩ := Cl3.cases hQ h
  rcases hc with hc | hc | hc | hc
  · exact caseA hQ h' hc
  · exact caseB hQ h' hc
  · exact caseC hQ h' hc
  · exact caseD hQ h' hc

end CFSG.GH74.E2
