module

public import CFSG.GH74.Generic.BProg.B2.Thm2Classes
public import CFSG.GH74.Generic.BProg.B2.GenLocL4ThreeFinal

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup

section Final5

theorem stage2Thm2C_of_unitary_classes
    (hExt : ∀ (F : Type) [Field F] [Finite F] (p f : ℕ), GenLocU4Inner.Su4ExtStmt F p f)
    (hQuat : ∀ (F : Type) [Field F] [Finite F] (p f : ℕ), GenLocU4Inner.Su4QuatStmt F p f)
    (hOut : ∀ (F : Type) [Field F] [Finite F] (p f : ℕ), GenLocU4Fam.Su4OuterStmt F p f) :
    Stage2Thm2C :=
  stage2Thm2C_of_classes (fun _ _ _ hF4 => genLoc4_sl4_lin_all hF4) hExt hQuat hOut

end Final5

end CFSG.GH74.Generic.BProg.B2
