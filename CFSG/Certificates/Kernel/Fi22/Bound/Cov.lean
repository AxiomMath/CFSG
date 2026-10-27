module

public import CFSG.Certificates.Kernel.MonsterConv.MatChain

public section

namespace CFSG.KC.Fi22B.Cov

open CFSG.KC.MonsterConv.MatChain

@[expose] noncomputable def M729 : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 729)) (nat_lit 1)

@[expose] noncomputable def m2 (A B : Nat) : Nat := mmul (nat_lit 27) (lows (nat_lit 27)) (nat_lit 134217727) A B

@[expose] noncomputable def mul4 (X Y : Nat) : Nat :=
  (fun x0 x1 y0 y1 => Nat.lor (Nat.xor (m2 x0 y0) (m2 x1 y1))
      (Nat.shiftLeft (Nat.xor (Nat.xor (m2 x0 y1) (m2 x1 y0)) (m2 x1 y1)) (nat_lit 729)))
    (Nat.land X M729) (Nat.shiftRight X (nat_lit 729)) (Nat.land Y M729) (Nat.shiftRight Y (nat_lit 729))

@[expose] noncomputable def one4 : Nat := ident (nat_lit 27)

@[expose] noncomputable def pw4 (X k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) one4 (fun _ acc => CFSG.KC.Loop.strictN acc (fun a => mul4 a X)) k

end CFSG.KC.Fi22B.Cov

end
