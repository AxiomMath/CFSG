module

public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Data.B_Sel
public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Data.T_Sel
public import CFSG.Certificates.Kernel.Common.LabF
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Lce
public import CFSG.Certificates.Kernel.Common.RelNorm
import CFSG.Certificates.Kernel.Bounds.CJSuz2.Checks.TH

public section

namespace CFSG.KC.CJSuz2.Route

theorem bot_sub : Nat.beq (CFSG.KD.CJSuz2B.selST (nat_lit 0)) (nat_lit 4) = true := by quickRfl

theorem bot_pow : Nat.beq (CFSG.KD.CJSuz2B.selRT (nat_lit 0)) (nat_lit 28380414028753969466561515933501938199330878594519746088102349021547335800) = true := by quickRfl

theorem order : Nat.beq (Nat.mul (Nat.mul CFSG.KD.CJSuz2T.nLive CFSG.KD.CJSuz2B.nLive) (nat_lit 30)) (nat_lit 1209600) = true := by quickRfl

end CFSG.KC.CJSuz2.Route

end
