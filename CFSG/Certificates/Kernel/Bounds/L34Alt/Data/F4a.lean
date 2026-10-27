module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
public import Init

#kc_repo #kc_nat_items_gz CFSG.KD.L34F4a "CFSG/Certificates/Kernel/Bounds/L34Alt/Data/F4a/tbl.items.gz" 15362 6276741304827307423
  TBL

public section

namespace CFSG.KD.L34F4a

@[expose] noncomputable def Tab (i : Nat) : Nat :=
  Nat.land (Nat.shiftRight TBL (Nat.mul i (nat_lit 32))) (nat_lit 4294967295)

@[expose] noncomputable def Cst (k : Nat) : Nat :=
  Nat.land (Nat.shiftRight (nat_lit 1666) (Nat.mul k (nat_lit 2))) (nat_lit 3)

end CFSG.KD.L34F4a

end
