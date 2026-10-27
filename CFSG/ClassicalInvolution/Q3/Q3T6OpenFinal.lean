module

public import CFSG.ClassicalInvolution.Q3.Q3T6OpenCore
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenMuUse
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenMuTab
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenSDFinal
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenEEnd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Disc3
open CFSG.Blueprint

section Open36


theorem thm6Open3_of (hB3 : GoldschmidtB3Tmp) : Thm6Open3 where
  notAllTypeTwo := notAllTypeTwoOfS3_of muZ2OfShape3
  mu := c19_2Three_of muS3OfShape3 muZ2OfShape3
  sd := c19_4Three_of_b3 hB3 muS3OfShape3
  e2 := c19_E2Prime3_of

end Open36

section Final


theorem thm6A3_of_gold (hB1 : S19B.GoldschmidtB1Tmp) (hB3 : GoldschmidtB3Tmp)
    (hM : Q3.M11Facts) (hOut : ∀ φ : MulAut ↥NativeSporadic.M11, ∃ g, φ = MulAut.conj g)
    (hL3 : ResidualL3Stmt) : Thm6A3 :=
  thm6A3_of_open3 (thm6Open3_of hB3) (c19_11b3_of hB1 hM hOut hL3)

end Final

end CFSG.ClassicalInvolution.Q3.Q3T6
