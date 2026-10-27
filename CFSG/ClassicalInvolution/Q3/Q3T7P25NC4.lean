module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25B00
public import CFSG.ClassicalInvolution.Asc77.AscC25J20
public import CFSG.ClassicalInvolution.Asc77.AscC25J21
public import CFSG.ClassicalInvolution.Q3.Q3T8Defs

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7P25

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.Q3T8.Asc77


theorem nc4Fact3_proved : Q3T8.Asc77.C25X.NC4Fact := by
  unfold Q3T8.Asc77.C25X.NC4Fact
  intro t k hadm h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact C25J.nc4SU_three (p := 3) (e := 1) hadm (by norm_num) (by norm_num)
  · exact C25J.nc4Spin7_three (p := 3) (e := 1) (by norm_num) hadm
  · exact C25J.nc4D4P_three (p := 3) (e := 1) (by norm_num) hadm
  · exact C25J.nc4D4M_three (p := 3) (e := 1) (by norm_num) hadm

end CFSG.ClassicalInvolution.Q3.Q3T7P25
