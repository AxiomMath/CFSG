module

public import CFSG.Certificates.Kernel.Fi22.Bound.Rels

public section

namespace CFSG.KC.Fi22K

@[expose] def E0 : Nat := nat_lit 21739618868010088828970512739672149675201596093512335998341424640432980107388

@[expose] def E1 : Nat := nat_lit 331720258606110974563148692927126243663038733847861030187547122699608180

@[expose] def E2 : Nat := nat_lit 5061649453828597634325388991197356455140279492364591521919141945452

@[expose] def E3 : Nat := nat_lit 77234641324288904332357620103969101193313130616732391898620004

@[expose] def E4 : Nat := nat_lit 77234641324288904332357620020893619107356116789645947334303844

@[expose] def E5 : Nat := nat_lit 331720258606110974563148692568915079477172400562344038452086501709717620

@[expose] noncomputable def subY (j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (nat_lit 0) E5 (Nat.beq j (nat_lit 12))) E4 (Nat.beq j (nat_lit 11))) E3 (Nat.beq j (nat_lit 10))) E2 (Nat.beq j (nat_lit 9))) E1 (Nat.beq j (nat_lit 8))) E0 (Nat.beq j (nat_lit 7))) (CFSG.KC.Fi22B.sub j) (Nat.blt j (nat_lit 7))

end CFSG.KC.Fi22K

end
