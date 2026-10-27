
module

public import CFSG.Certificates.Kernel.KDense.Data.Tab
public import CFSG.Certificates.Kernel.KDense.Y443.Pairs
public import CFSG.Certificates.Kernel.Common.Chain
public import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.YGroups.Y443.Native.EdgeNoncommBase
public import Certificates.Data.Kernel.KDense.Chunk

public section

set_option maxRecDepth 100000

namespace CFSG.KD.Y443.c10115

open CFSG.KC.KDense

@[expose] noncomputable def run (σ c : Nat) (s : St) : St :=
  CFSG.KC.KDense.run CFSG.KD.KDF.F CFSG.KD.KDT.T (Y443.words Y443.p10115 σ)
    (f20 c (nat_lit 1)) (f20 c (nat_lit 2)) s

end CFSG.KD.Y443.c10115

#kc_chain CFSG.KD.Y443.c10115 CFSG.KD.Y443.c10115.run "c10115.plan.txt" 3090 12204216901218879392
#kc_select CFSG.KD.Y443.c10115 Xf X 39
#kc_select CFSG.KD.Y443.c10115 Af A 39
#kc_select CFSG.KD.Y443.c10115 Wf W 39
#kc_select CFSG.KD.Y443.c10115 CH CH 72

namespace CFSG.KD.Y443.c10115

open CFSG.KC.KDense

@[expose] noncomputable def S (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (Xf j) (Af j) (Wf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

end CFSG.KD.Y443.c10115

end
