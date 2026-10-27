module

public import CFSG.GH74.Generic.BProg.B2.Thm2Unitary
public import CFSG.GH74.Generic.BProg.B2.GenLocU4Ext
public import CFSG.GH74.Generic.BProg.B2.GenLocU4Q
public import CFSG.GH74.Generic.BProg.B2.GenLocU4Q2s
public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutAsm
public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutGenExt
public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutDa

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup

section Done


theorem thm2Done_extStmt
    (K : Type) [Field K] [Finite K] (p f : ℕ) : GenLocU4Inner.Su4ExtStmt K p f :=
  fun hp hp2 hK hq {_} _ _ α hA ρ hU hρ hab a₀ c hc hsq =>
    GenLocU4Ext.gammaAct_su4_ext hp hp2 hK hq α hA ρ hU hρ hab a₀ c hc hsq

theorem thm2Done_quatStmt
    (K : Type) [Field K] [Finite K] (p f : ℕ) : GenLocU4Inner.Su4QuatStmt K p f :=
  GenLocU4Q.su4QuatStmt GenLocU4Q2.su4Q2Stmt_holds GenLocU4Q2s.su4Q2SplitStmt_holds

theorem thm2Done_outerStmt
    (K : Type) [Field K] [Finite K] (p f : ℕ) : GenLocU4Fam.Su4OuterStmt K p f :=
  fun hp hp2 hK hq {_} _ _ α hA hout hsect =>
    GenLocU4OutAsm.gammaAct_su4_outer_of_classes (GenLocU4Out.outSplitGen K p f) (GenLocU4Out.outDbGen K p f)
      (GenLocU4Out.outExtGen K p f) GenLocU4OutDa.outDaGen_holds hp hp2 hK hq α hA hout hsect

theorem stage2Thm2C_proved
    : Stage2Thm2C :=
  stage2Thm2C_of_unitary_classes thm2Done_extStmt thm2Done_quatStmt thm2Done_outerStmt

theorem stage2Thm2_proved
    : Stage2Thm2 :=
  stage2Thm2_of_C stage2Thm2C_proved

end Done

end CFSG.GH74.Generic.BProg.B2
