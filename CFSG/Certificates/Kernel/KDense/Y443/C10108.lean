
module

public import CFSG.Certificates.Kernel.KDense.Data.Tab
public import CFSG.Certificates.Kernel.KDense.Y443.Pairs
public import CFSG.Certificates.Kernel.Common.Chain
public import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.YGroups.Y443.Native.EdgeNoncommBase
public import Certificates.Data.Kernel.KDense.Chunk

public section

set_option maxRecDepth 100000

namespace CFSG.KD.Y443.c10108

open CFSG.KC.KDense

@[expose] noncomputable def run (σ c : Nat) (s : St) : St :=
  CFSG.KC.KDense.run CFSG.KD.KDF.F CFSG.KD.KDT.T (Y443.words Y443.pAlign σ)
    (f20 c (nat_lit 1)) (f20 c (nat_lit 2)) s

end CFSG.KD.Y443.c10108

#kc_chain CFSG.KD.Y443.c10108 CFSG.KD.Y443.c10108.run "c10108.plan.txt" 1095 9610428669009740348
#kc_select CFSG.KD.Y443.c10108 Xf X 28
#kc_select CFSG.KD.Y443.c10108 Af A 28
#kc_select CFSG.KD.Y443.c10108 Wf W 28
#kc_select CFSG.KD.Y443.c10108 CH CH 29

namespace CFSG.KD.Y443.c10108

open CFSG.KC.KDense

@[expose] noncomputable def S (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (Xf j) (Af j) (Wf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

end CFSG.KD.Y443.c10108

end
