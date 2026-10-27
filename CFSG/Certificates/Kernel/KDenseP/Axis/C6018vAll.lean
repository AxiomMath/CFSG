module

public import CFSG.Certificates.Kernel.KDenseP.Axis.C6018v
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 200000

#kc_repo #kc_items_root CFSG.KD.AX.c6018v.VAL "CFSG/Certificates/Kernel/KDenseP/Axis/c6018v_val.bin" 180 8845619168564730258

namespace CFSG.KD.AX.c6018v

theorem weq : CFSG.KC.KDenseP.wordsEqB WD
    (CFSG.KC.KDense.Y443.words CFSG.KC.KDenseP.Axis.p6018v) (nat_lit 24) = true := by
  quickRfl

@[expose] noncomputable def v (t : Nat) : Bool :=
  CFSG.KC.KDenseP.valOK (nat_lit 7) (S (VAL (3 * t))) (VAL (3 * t + 1)) (VAL (3 * t + 2))

@[expose] noncomputable def t (k : Nat) : Bool :=
  CFSG.KC.KDenseP.chunkOKN (nat_lit 7) (nat_lit 3) (nat_lit 127) CFSG.KD.KDF.F CFSG.KD.AXM.MT WL S
    (CH k)

end CFSG.KD.AX.c6018v

#kc_each CFSG.KD.AX.c6018v.v 0 12
#kc_each CFSG.KD.AX.c6018v.t 0 24

end
