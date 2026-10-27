module

public import CFSG.Certificates.Kernel.KDenseP.DenseAlign.Run
public import CFSG.Certificates.Kernel.KDenseP.DenseAlign.Pairs
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.YGroups.Y443.Native.EdgeNoncommBase

public section

set_option maxRecDepth 100000

open CFSG.KC.KDenseP.HeSeven CFSG.KC.KDenseP.DenseAlign in
@[expose] noncomputable def CFSG.KD.DA7.c17594.run := CFSG.KD.DA7.runP (tri e17594 [])

#kc_chain CFSG.KD.DA7.c17594 CFSG.KD.DA7.c17594.run "c17594.plan.txt" 1200 13333758976383265277
#kc_select CFSG.KD.DA7.c17594 Xf X 33
#kc_select CFSG.KD.DA7.c17594 Af A 33
#kc_select CFSG.KD.DA7.c17594 Wf W 33
#kc_select CFSG.KD.DA7.c17594 CH CH 36

namespace CFSG.KD.DA7.c17594

open CFSG.KC.KDense CFSG.KC.KDenseP.HeSeven CFSG.KC.KDenseP.DenseAlign

@[expose] noncomputable def S (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (Xf j) (Af j) (Wf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def t (k : Nat) : Bool := chkP (tri e17594 []) S (CH k)

end CFSG.KD.DA7.c17594

#kc_each CFSG.KD.DA7.c17594.t 0 36

end
