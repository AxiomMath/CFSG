module

public import Init

public section

namespace CFSG.KC.U43Alt

@[expose] def R0 : Nat := nat_lit 8

@[expose] def R1 : Nat := nat_lit 9042521604759576

@[expose] def R2 : Nat := nat_lit 249234052219501735656397057400242232

@[expose] def R3 : Nat := nat_lit 716411482204249450819566081704855070792745032

@[expose] def R4 : Nat := nat_lit 46950744297042338505161404781097918834007104036944

@[expose] def R5 : Nat :=
  nat_lit 84809525197700553233272103563090620931725308396551952548503364766507466872

@[expose] def R6 : Nat :=
  nat_lit 7416735495152974194369648581354219727158081248930472264157172525955811872207502521343574431022637174937107583467708

@[expose] def R7 : Nat :=
  nat_lit 4090048584480162701112135032936372475687677399463520140271843855567287594366152833222316180

@[expose] def R8 : Nat :=
  nat_lit 26349671140806703304576381373645775310698541814039815416455833640089574247231116485043688637116461220

@[expose] def S0 : Nat := nat_lit 8196

@[expose] noncomputable def rel (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat)
    (nat_lit 0) R8 (Nat.beq k (nat_lit 8))) R7 (Nat.beq k (nat_lit 7))) R6 (Nat.beq k (nat_lit 6)))
    R5 (Nat.beq k (nat_lit 5))) R4 (Nat.beq k (nat_lit 4))) R3 (Nat.beq k (nat_lit 3)))
    R2 (Nat.beq k (nat_lit 2))) R1 (Nat.beq k (nat_lit 1))) R0 (Nat.beq k (nat_lit 0))

@[expose] noncomputable def sub (j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0) S0 (Nat.beq j (nat_lit 0))

@[expose] def relCodes : List (List Nat) :=
  [[nat_lit 0, nat_lit 0],
    [nat_lit 2, nat_lit 2, nat_lit 2, nat_lit 2, nat_lit 2, nat_lit 2],
    [nat_lit 0, nat_lit 3, nat_lit 0, nat_lit 3, nat_lit 0, nat_lit 3, nat_lit 0, nat_lit 3, nat_lit 0,
      nat_lit 3, nat_lit 0, nat_lit 3, nat_lit 0, nat_lit 3],
    [nat_lit 0, nat_lit 2, nat_lit 2, nat_lit 0, nat_lit 3, nat_lit 3, nat_lit 0, nat_lit 3, nat_lit 3,
      nat_lit 0, nat_lit 3, nat_lit 3, nat_lit 0, nat_lit 2, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 2],
    [nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 2, nat_lit 2, nat_lit 0, nat_lit 3, nat_lit 3, nat_lit 3,
      nat_lit 0, nat_lit 3, nat_lit 3, nat_lit 3, nat_lit 0, nat_lit 3, nat_lit 3, nat_lit 3, nat_lit 0,
      nat_lit 2, nat_lit 2],
    [nat_lit 0, nat_lit 3, nat_lit 3, nat_lit 0, nat_lit 2, nat_lit 0, nat_lit 3, nat_lit 3, nat_lit 0,
      nat_lit 3, nat_lit 0, nat_lit 2, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 0, nat_lit 3, nat_lit 3,
      nat_lit 0, nat_lit 3, nat_lit 0, nat_lit 3, nat_lit 3, nat_lit 0, nat_lit 2, nat_lit 0, nat_lit 2,
      nat_lit 2, nat_lit 0, nat_lit 3],
    [nat_lit 0, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 2, nat_lit 2, nat_lit 0,
      nat_lit 3, nat_lit 0, nat_lit 3, nat_lit 3, nat_lit 0, nat_lit 3, nat_lit 0, nat_lit 3, nat_lit 3,
      nat_lit 0, nat_lit 3, nat_lit 0, nat_lit 3, nat_lit 0, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 2,
      nat_lit 0, nat_lit 3, nat_lit 0, nat_lit 2, nat_lit 2, nat_lit 0, nat_lit 3, nat_lit 3, nat_lit 3,
      nat_lit 0, nat_lit 2, nat_lit 2, nat_lit 0, nat_lit 3, nat_lit 0, nat_lit 3, nat_lit 3, nat_lit 0,
      nat_lit 3, nat_lit 3]]

@[expose] def coverCodes : List (List Nat) :=
  [[nat_lit 1, nat_lit 2, nat_lit 0, nat_lit 3, nat_lit 0, nat_lit 3, nat_lit 3, nat_lit 0, nat_lit 2,
      nat_lit 2, nat_lit 2, nat_lit 1, nat_lit 3, nat_lit 3, nat_lit 3, nat_lit 1, nat_lit 2, nat_lit 2,
      nat_lit 1, nat_lit 2, nat_lit 0, nat_lit 3, nat_lit 0, nat_lit 2, nat_lit 3, nat_lit 3, nat_lit 3,
      nat_lit 0, nat_lit 3, nat_lit 1, nat_lit 2, nat_lit 1, nat_lit 3, nat_lit 1, nat_lit 2, nat_lit 2,
      nat_lit 2],
    [nat_lit 3, nat_lit 0, nat_lit 2, nat_lit 0, nat_lit 3, nat_lit 0, nat_lit 2, nat_lit 0, nat_lit 2,
      nat_lit 1, nat_lit 3, nat_lit 1, nat_lit 3, nat_lit 1, nat_lit 3, nat_lit 1, nat_lit 2, nat_lit 0,
      nat_lit 3, nat_lit 3, nat_lit 0, nat_lit 2, nat_lit 2, nat_lit 2, nat_lit 2, nat_lit 0, nat_lit 2,
      nat_lit 0, nat_lit 3, nat_lit 3, nat_lit 3, nat_lit 1, nat_lit 2, nat_lit 2, nat_lit 1, nat_lit 2,
      nat_lit 1, nat_lit 3, nat_lit 1, nat_lit 3, nat_lit 3]]

end CFSG.KC.U43Alt

end
