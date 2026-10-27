module

import CFSG.Certificates.Kernel.Common.Harness
public import Init
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_nat_items_gz CFSG.KD.U43M3 "CFSG/Certificates/Kernel/Bounds/U43Alt/Data/data/M3/tbl.items.gz" 8642 2832935088425692707
  TBL

public section

namespace CFSG.KD.U43M3

@[expose] noncomputable def Tab (i : Nat) : Nat :=
  Nat.land (Nat.shiftRight TBL (Nat.mul i (nat_lit 32))) (nat_lit 4294967295)

@[expose] noncomputable def Cst (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (Nat.beq k (nat_lit 6))

end CFSG.KD.U43M3

end
