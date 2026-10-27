module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4Inner
public import CFSG.GH74.Generic.BProg.B2.GenLocL4Q

public section

namespace CFSG.GH74.Generic.BProg.B2

namespace GenLocL4Final

theorem quatStmt (F : Type) [Field F] [Finite F] : GenLocL4Inner.Sl4QuatStmt F :=
  fun hF hF4 h7 {_} _ _ α hA hinner hsect x y a b hax hby hanti =>
    gammaAct_sl4_quat hF hF4 h7 α hA hinner hsect x y a b hax hby hanti

end GenLocL4Final

end CFSG.GH74.Generic.BProg.B2
