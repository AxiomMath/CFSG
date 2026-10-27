module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CFSG.KC.McL.Rels

#kc_repo #kc_nat_items_gz CFSG.KC.McL.Rels
  "CFSG/Certificates/Kernel/McL/Data/Rels.items.gz" 3082 2223534432091229750
  X[8] Q[78] G[34] M[6] S[3] U[3] H[3]

#kc_repo #kc_json_gz CFSG.KC.McL.Rels
  "CFSG/Certificates/Kernel/McL/Data/Rels.json.gz" 99 15174115536156676103
  (K1W : Nat) (SQ : Nat) (P5 : Nat)

end CFSG.KC.McL.Rels

end

#kc_select CFSG.KC.McL.Rels XT X 8
#kc_select CFSG.KC.McL.Rels QR Q 78
#kc_select CFSG.KC.McL.Rels GR G 34
#kc_select CFSG.KC.McL.Rels MG M 6
#kc_select CFSG.KC.McL.Rels KS S 3
#kc_select CFSG.KC.McL.Rels KQ U 3
#kc_select CFSG.KC.McL.Rels KH H 3

public section

namespace CFSG.KC.McL.Rels

@[expose] noncomputable def XD (g : Nat) : Nat := XT (Nat.mul (nat_lit 2) g)

@[expose] noncomputable def NR1 (r : Nat) : Nat := Bool.rec (motive := fun _ => Nat) K1W (QR r) (Nat.blt r (nat_lit 78))

@[expose] noncomputable def STQ (_ : Nat) : Nat := SQ

end CFSG.KC.McL.Rels

end
