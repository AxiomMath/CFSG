module

public import Init

public section

namespace CFSG.KC.Co2K

@[expose] def G1 : Nat := nat_lit 4

@[expose] def G2 : Nat := nat_lit 536883212

@[expose] def G3 : Nat := nat_lit 35321814200340

@[expose] def G4 : Nat := nat_lit 327063797141267012745340814098484

@[expose] def G5 : Nat := nat_lit 52982718668820

@[expose] noncomputable def gen (k : Nat) : Nat :=
  (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (nat_lit 0) G5 (Nat.beq k (nat_lit 5))) G4 (Nat.beq k (nat_lit 4))) G3 (Nat.beq k (nat_lit 3))) G2 (Nat.beq k (nat_lit 2))) G1 (Nat.beq k (nat_lit 1)))

@[expose] noncomputable def subH (j : Nat) : Nat :=
  (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (nat_lit 0) G5 (Nat.beq j (nat_lit 3))) G3 (Nat.beq j (nat_lit 2))) G2 (Nat.beq j (nat_lit 1))) G1 (Nat.beq j (nat_lit 0)))

end CFSG.KC.Co2K

end
