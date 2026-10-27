module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
public import Init

#kc_repo #kc_nat_items_gz CFSG.KD.L34P3 "CFSG/Certificates/Kernel/Bounds/L34Alt/Data/P3/tbl.items.gz" 337 11500099656425255975
  TBL

public section

namespace CFSG.KD.L34P3

@[expose] noncomputable def Tab (i : Nat) : Nat :=
  Nat.land (Nat.shiftRight TBL (Nat.mul i (nat_lit 32))) (nat_lit 4294967295)

@[expose] noncomputable def Cst (k : Nat) : Nat :=
  Nat.land (Nat.shiftRight (nat_lit 5282) (Nat.mul k (nat_lit 2))) (nat_lit 3)

end CFSG.KD.L34P3

end
