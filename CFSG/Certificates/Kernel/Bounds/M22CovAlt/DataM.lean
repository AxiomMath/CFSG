module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Bounds.LoadGz
public import Certificates.Data.Kernel.Multipliers.Mono

#kc_repo #kc_nat_items_gz CFSG.KD.M22M "CFSG/Certificates/Kernel/Bounds/M22CovAlt/data/M.items.gz" 42243 2976230268761826742
  TBL

public section

namespace CFSG.KD.M22M

@[expose] noncomputable def Tab (i : Nat) : Nat :=
  Nat.land (Nat.shiftRight TBL (Nat.mul i (nat_lit 32))) (nat_lit 4294967295)

@[expose] noncomputable def Cst (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 9) (Nat.beq k (nat_lit 5)))
    (nat_lit 1) (Nat.beq k (nat_lit 2))

@[expose] def Rc : List (List Nat) :=
  [[0, 0, 0, 0, 2, 1, 2, 1, 2], [0, 0, 2, 1, 3, 0, 2, 2, 1, 3], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
    [0, 0, 0, 0, 0], [0, 3, 0, 3, 0, 3], [0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2]]

@[expose] def Wc : List (List Nat) :=
  [[1, 3, 1, 2, 1, 3, 0, 2, 0, 0, 2, 0, 0, 3, 3, 1, 2, 1, 1],
    [3, 0, 3, 3, 1, 1, 3, 1, 2, 2, 2, 1, 3, 0, 2, 0, 0]]

@[expose] noncomputable def pt (x : Nat) : Bool :=
  CFSG.KC.Mono.pointOK Tab (nat_lit 2) (nat_lit 2640) (nat_lit 12) Cst Rc Wc x

end CFSG.KD.M22M

end
