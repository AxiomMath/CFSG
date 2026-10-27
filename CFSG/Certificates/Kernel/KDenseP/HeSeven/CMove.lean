module

public import CFSG.Certificates.Kernel.KDenseP.HeSeven.Run
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.YGroups.Y443.Native.EdgeNoncommBase

public section

set_option maxRecDepth 100000

open CFSG.KC.KDenseP.HeSeven in
@[expose] noncomputable def CFSG.KD.HE7.cmove.run := CFSG.KD.HE7.runP (tri [] nHe)

#kc_chain CFSG.KD.HE7.cmove CFSG.KD.HE7.cmove.run "cmove.plan.txt" 1274 7133913491209632306
#kc_select CFSG.KD.HE7.cmove Xf X 37
#kc_select CFSG.KD.HE7.cmove Af A 37
#kc_select CFSG.KD.HE7.cmove Wf W 37
#kc_select CFSG.KD.HE7.cmove CH CH 39

namespace CFSG.KD.HE7.cmove

open CFSG.KC.KDense CFSG.KC.KDenseP.HeSeven

@[expose] noncomputable def S (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (Xf j) (Af j) (Wf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def t (k : Nat) : Bool := chkP (tri [] nHe) S (CH k)

end CFSG.KD.HE7.cmove

#kc_each CFSG.KD.HE7.cmove.t 0 39

end
