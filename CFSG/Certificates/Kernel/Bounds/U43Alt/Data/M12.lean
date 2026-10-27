module

import CFSG.Certificates.Kernel.Common.Harness
public import Init
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_nat_items_gz CFSG.KD.U43M12 "CFSG/Certificates/Kernel/Bounds/U43Alt/Data/data/M12/tbl.items.gz" 8643 10998050910827758624
  TBL

public section

namespace CFSG.KD.U43M12

@[expose] noncomputable def Tab (i : Nat) : Nat :=
  Nat.land (Nat.shiftRight TBL (Nat.mul i (nat_lit 32))) (nat_lit 4294967295)

@[expose] noncomputable def Cst (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
    (nat_lit 9) (Nat.beq k (nat_lit 6))) (nat_lit 4) (Nat.beq k (nat_lit 5)))
    (nat_lit 3) (Nat.beq k (nat_lit 4))) (nat_lit 6) (Nat.beq k (nat_lit 3)))
    (nat_lit 6) (Nat.beq k (nat_lit 0))

end CFSG.KD.U43M12

end
