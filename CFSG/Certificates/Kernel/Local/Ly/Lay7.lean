module

public import CFSG.Certificates.Kernel.Orders.Mat
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CFSG.KC.LL.Ly7

#kc_repo #kc_json_gz CFSG.KC.LL.Ly7
  "CFSG/Certificates/Kernel/Local/Ly/data/Lay7.json.gz" 552 4867022115096163093
  (L7 : Nat) (H7 : Nat) (CM7 : Nat) (RM7 : Nat) (ONE7 : Nat) (LV7 : Nat) (HV7 : Nat)

@[expose] noncomputable def mul7 (A B : Nat) : Nat := CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 8) (nat_lit 56) (nat_lit 7) (nat_lit 4) L7 H7 CM7 RM7 A B

@[expose] noncomputable def vec7 (v M : Nat) : Nat := CFSG.KC.Ord.vecR (nat_lit 5) (nat_lit 8) (nat_lit 56) (nat_lit 7) (nat_lit 4) LV7 HV7 RM7 v M

@[expose] noncomputable def ent7 (X i j : Nat) : Nat := CFSG.KC.Ord.bitsN X (Nat.add (Nat.mul (nat_lit 56) i) (Nat.mul (nat_lit 8) j)) (nat_lit 8)

@[expose] noncomputable def ent111 (X i j : Nat) : Nat := CFSG.KC.Ord.bitsN X (Nat.add (Nat.mul (nat_lit 1332) i) (Nat.mul (nat_lit 12) j)) (nat_lit 12)

@[expose] noncomputable def blockOf (X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.lor acc (Nat.shiftLeft (ent111 X (Nat.div k (nat_lit 7)) (Nat.mod k (nat_lit 7)))
      (Nat.add (Nat.mul (nat_lit 56) (Nat.div k (nat_lit 7))) (Nat.mul (nat_lit 8) (Nat.mod k (nat_lit 7)))))) (nat_lit 49)

end CFSG.KC.LL.Ly7

end
