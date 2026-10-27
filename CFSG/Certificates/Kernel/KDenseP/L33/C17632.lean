module

public import CFSG.Certificates.Kernel.KDenseP.L33.Run
public import CFSG.Certificates.Kernel.KDenseP.L33.Pairs
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

open CFSG.KC.KDenseP.HeSeven CFSG.KC.KDenseP.L33 in
@[expose] noncomputable def CFSG.KD.L33.c17632.run := CFSG.KD.L33.runP (tri e17632 [])

#kc_chain CFSG.KD.L33.c17632 CFSG.KD.L33.c17632.run "c17632.plan.txt" 3958 11877695216362827040
#kc_select CFSG.KD.L33.c17632 Xf X 93
#kc_select CFSG.KD.L33.c17632 Af A 93
#kc_select CFSG.KD.L33.c17632 Wf W 93
#kc_select CFSG.KD.L33.c17632 CH CH 114

namespace CFSG.KD.L33.c17632

open CFSG.KC.KDense CFSG.KC.KDenseP.HeSeven CFSG.KC.KDenseP.L33

@[expose] noncomputable def S (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (Xf j) (Af j) (Wf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def t (k : Nat) : Bool := chkP (tri e17632 []) S (CH k)

end CFSG.KD.L33.c17632

#kc_each CFSG.KD.L33.c17632.t 0 114

end
