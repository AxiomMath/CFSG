module

public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6073
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 200000

namespace CFSG.KD.TP.c6073

theorem weq : CFSG.KC.KDenseP.wordsEqB WD
    (CFSG.KC.KDense.Y443.words CFSG.KC.KDenseP.TwoPoint.p6073) (nat_lit 18) = true := by
  quickRfl

@[expose] noncomputable def u (g : Nat) : Bool :=
  CFSG.KC.KDenseP.grpL rn
    (CFSG.KC.KDenseP.chunkOKN (nat_lit 4) (nat_lit 2) (nat_lit 5) CFSG.KD.KDF.F CFSG.KD.TPM.MT WL)
    CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

end CFSG.KD.TP.c6073

#kc_each CFSG.KD.TP.c6073.u 0 5

end
