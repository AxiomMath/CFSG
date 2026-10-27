module

public import CFSG.ClassicalInvolution.Q3.Q3T6OpenL3
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenFinal
public import CFSG.ClassicalInvolution.Q3.Q3T6FusM11Out
public import CFSG.ClassicalInvolution.AschTight.S19BMain
public import CFSG.ClassicalInvolution.AschTight.Thm6TightB3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Disc3

section Proved


theorem thm6A3_proved : Thm6A3 :=
  thm6A3_of_gold S19B.goldschmidtB1Tmp_holds goldschmidtB3Tmp_holds Q3.m11Facts
    (m11_outer_trivial Q3.m11Facts) residualL3Stmt

end Proved

end CFSG.ClassicalInvolution.Q3.Q3T6
