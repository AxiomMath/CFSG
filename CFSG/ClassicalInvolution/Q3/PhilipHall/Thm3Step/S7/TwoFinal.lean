module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.TwoMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.TwoL3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.TwoCoinc

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident

section Main

theorem twoOrbitOfIdent'_of_finite (hTL : TwoLieOrbitsSame) (hOC : SocleOddCore)
    (hTO : TwinOddCore) (hL33 : L33Q8Class) (hU3 : U33Q8Classes) (hM12 : M12Q8Classes)
    (hTQ : TwinQ8Class) : TwoOrbitOfIdent' :=
  twoOrbitOfIdent'_of_facts hTL l3CentComponent coincTwin hOC hTO hL33 hU3 hM12 hTQ

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident
