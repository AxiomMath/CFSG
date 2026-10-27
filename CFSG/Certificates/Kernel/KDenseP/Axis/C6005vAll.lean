module

public import CFSG.Certificates.Kernel.KDenseP.Axis.C6005v
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 200000

#kc_repo #kc_items_root CFSG.KD.AX.c6005v.VAL "CFSG/Certificates/Kernel/KDenseP/Axis/c6005v_val.bin" 150 9364187239943048583

namespace CFSG.KD.AX.c6005v

theorem weq : CFSG.KC.KDenseP.wordsEqB WD
    (CFSG.KC.KDense.Y443.words CFSG.KC.KDenseP.Axis.p6005v) (nat_lit 20) = true := by
  quickRfl

@[expose] noncomputable def v (t : Nat) : Bool :=
  CFSG.KC.KDenseP.valOK (nat_lit 7) (S (VAL (3 * t))) (VAL (3 * t + 1)) (VAL (3 * t + 2))

@[expose] noncomputable def t (k : Nat) : Bool :=
  CFSG.KC.KDenseP.chunkOKN (nat_lit 7) (nat_lit 3) (nat_lit 127) CFSG.KD.KDF.F CFSG.KD.AXM.MT WL S
    (CH k)

end CFSG.KD.AX.c6005v

#kc_each CFSG.KD.AX.c6005v.v 0 10
#kc_each CFSG.KD.AX.c6005v.t 0 19

end
