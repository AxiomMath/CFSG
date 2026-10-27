module

public import CFSG.Certificates.Kernel.KDenseP.HeSeven.Run
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.YGroups.Y443.Native.EdgeNoncommBase

public section

set_option maxRecDepth 100000

open CFSG.KC.KDenseP.HeSeven in
@[expose] noncomputable def CFSG.KD.HE7.cfix.run := CFSG.KD.HE7.runP (tri eHe [])

#kc_chain CFSG.KD.HE7.cfix CFSG.KD.HE7.cfix.run "cfix.plan.txt" 6257 7729628266188053881
#kc_select CFSG.KD.HE7.cfix Xf X 126
#kc_select CFSG.KD.HE7.cfix Af A 126
#kc_select CFSG.KD.HE7.cfix Wf W 126
#kc_select CFSG.KD.HE7.cfix CH CH 171

namespace CFSG.KD.HE7.cfix

open CFSG.KC.KDense CFSG.KC.KDenseP.HeSeven

@[expose] noncomputable def S (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (Xf j) (Af j) (Wf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def t (k : Nat) : Bool := chkP (tri eHe []) S (CH k)

end CFSG.KD.HE7.cfix

#kc_each CFSG.KD.HE7.cfix.t 0 171

end
