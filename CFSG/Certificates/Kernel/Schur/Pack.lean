module


public section

namespace CFSG.KC.Schur.Pack

@[expose] noncomputable def code (x : Nat × Bool) : Nat :=
  Prod.rec (motive := fun _ => Nat)
    (fun g b => Bool.rec (motive := fun _ => Nat) (Nat.add (Nat.mul (nat_lit 2) g) (nat_lit 1))
      (Nat.mul (nat_lit 2) g) b) x

@[expose] noncomputable def pk (w : List (Nat × Bool)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.lor (code x) (Nat.shiftLeft ih (nat_lit 8))) w

end CFSG.KC.Schur.Pack

end
