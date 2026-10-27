module

public import CFSG.Certificates.Kernel.KDenseP.Axis.C6009
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 200000

namespace CFSG.KD.AX.c6009

theorem weq : CFSG.KC.KDenseP.wordsEqB WD
    (CFSG.KC.KDense.Y443.words CFSG.KC.KDenseP.Axis.p6009) (nat_lit 84) = true := by
  quickRfl

@[expose] noncomputable def t (k : Nat) : Bool :=
  CFSG.KC.KDenseP.chunkOKN (nat_lit 3) (nat_lit 2) (nat_lit 7) CFSG.KD.KDF.F CFSG.KD.AXM.MT WL S
    (CH k)

end CFSG.KD.AX.c6009

#kc_each CFSG.KD.AX.c6009.t 0 15

end
