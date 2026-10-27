module

public import CFSG.Certificates.Kernel.KDenseP.Axis.C6003
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 200000

namespace CFSG.KD.AX.c6003

theorem weq : CFSG.KC.KDenseP.wordsEqB WD
    (CFSG.KC.KDense.Y443.words CFSG.KC.KDenseP.Axis.p6003) (nat_lit 258) = true := by
  quickRfl

@[expose] noncomputable def t (k : Nat) : Bool :=
  CFSG.KC.KDenseP.chunkOKN (nat_lit 3) (nat_lit 2) (nat_lit 7) CFSG.KD.KDF.F CFSG.KD.AXM.MT WL S
    (CH k)

end CFSG.KD.AX.c6003

#kc_each CFSG.KD.AX.c6003.t 0 140

end
