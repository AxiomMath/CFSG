module

public import CFSG.Certificates.Kernel.KDenseP.Q7.Run
public import CFSG.Certificates.Kernel.KDenseP.Q7.Pairs
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.YGroups.Y443.Native.EdgeNoncomm

public section

set_option maxRecDepth 100000

open CFSG.KC.KDenseP.MonThreeB CFSG.KC.KDenseP.Q7 in
@[expose] noncomputable def CFSG.KD.Q7.c17487.run := CFSG.KD.Q7.runP (tri q7Eqs q7Nes)

#kc_chain CFSG.KD.Q7.c17487 CFSG.KD.Q7.c17487.run "c17487.plan.txt" 3894 16808881405259414113
#kc_select CFSG.KD.Q7.c17487 Xf X 63
#kc_select CFSG.KD.Q7.c17487 Af A 63
#kc_select CFSG.KD.Q7.c17487 Wf W 63
#kc_select CFSG.KD.Q7.c17487 CH CH 99

namespace CFSG.KD.Q7.c17487

open CFSG.KC.KDense CFSG.KC.KDenseP.MonThreeB CFSG.KC.KDenseP.Q7

@[expose] noncomputable def S (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (Xf j) (Af j) (Wf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def t (k : Nat) : Bool := CFSG.KD.Q7.chkP (tri q7Eqs q7Nes) S (CH k)

end CFSG.KD.Q7.c17487

#kc_each CFSG.KD.Q7.c17487.t 0 99

end
