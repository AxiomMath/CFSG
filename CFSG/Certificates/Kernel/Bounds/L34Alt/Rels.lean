module

public import Init

public section

namespace CFSG.KC.L34Alt

@[expose] def relCodes : List (List Nat) :=
  [[nat_lit 0, nat_lit 0],
    [nat_lit 2, nat_lit 2, nat_lit 2, nat_lit 2, nat_lit 2],
    [nat_lit 0, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 0, nat_lit 2,
      nat_lit 0, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 0, nat_lit 2],
    [nat_lit 0, nat_lit 2, nat_lit 0, nat_lit 3, nat_lit 0, nat_lit 2, nat_lit 0, nat_lit 3,
      nat_lit 0, nat_lit 2, nat_lit 0, nat_lit 3, nat_lit 0, nat_lit 2, nat_lit 0, nat_lit 3],
    [nat_lit 0, nat_lit 2, nat_lit 2, nat_lit 1, nat_lit 3, nat_lit 3, nat_lit 0, nat_lit 2,
      nat_lit 2, nat_lit 1, nat_lit 3, nat_lit 3, nat_lit 0, nat_lit 2, nat_lit 2, nat_lit 1,
      nat_lit 3, nat_lit 3],
    [nat_lit 0, nat_lit 2, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 2, nat_lit 0, nat_lit 2,
      nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 2, nat_lit 0,
      nat_lit 2, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 2],
    [nat_lit 0, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 2, nat_lit 0, nat_lit 3, nat_lit 0,
      nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 2, nat_lit 0, nat_lit 3, nat_lit 0, nat_lit 2,
      nat_lit 0, nat_lit 2, nat_lit 2, nat_lit 0, nat_lit 3, nat_lit 0, nat_lit 2, nat_lit 0,
      nat_lit 2, nat_lit 2, nat_lit 0, nat_lit 3, nat_lit 0, nat_lit 2, nat_lit 0, nat_lit 2,
      nat_lit 2, nat_lit 0, nat_lit 3, nat_lit 0, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 2,
      nat_lit 0, nat_lit 3, nat_lit 0, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 2, nat_lit 0,
      nat_lit 3]]

@[expose] def coverCodes : List (List Nat) :=
  [[nat_lit 1, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 0, nat_lit 3, nat_lit 0, nat_lit 3,
      nat_lit 0, nat_lit 3, nat_lit 1, nat_lit 3, nat_lit 1, nat_lit 2, nat_lit 1, nat_lit 2,
      nat_lit 1, nat_lit 3, nat_lit 3, nat_lit 3, nat_lit 0, nat_lit 2, nat_lit 1, nat_lit 2,
      nat_lit 2],
    [nat_lit 3, nat_lit 3, nat_lit 3, nat_lit 0, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 0,
      nat_lit 2, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 0, nat_lit 2,
      nat_lit 2, nat_lit 1, nat_lit 3, nat_lit 1, nat_lit 3, nat_lit 1, nat_lit 3, nat_lit 3,
      nat_lit 1, nat_lit 3, nat_lit 1, nat_lit 3, nat_lit 1]]

@[expose] noncomputable def rel (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat)
  (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat)
  (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat)
  (nat_lit 0)
  (nat_lit 111723723757407124177055704559436902443391041191348543066258166179180660)
    (Nat.beq k (nat_lit 8)))
  (nat_lit 51623280055740033183100348128613096766579992093701372431568996) (Nat.beq k (nat_lit 7)))
  (nat_lit 484176796631624322495777756775704234471844921496505533104487659962481503259334934684981981053613856854750931082991894724)
    (Nat.beq k (nat_lit 6)))
  (nat_lit 12019390181820827803555282281388554871430578236817492) (Nat.beq k (nat_lit 5)))
  (nat_lit 1074622646473518320065165930555191327612469320) (Nat.beq k (nat_lit 4)))
  (nat_lit 16333719769507509847922462728174583152704) (Nat.beq k (nat_lit 3)))
  (nat_lit 166156034813001157104264704933494840) (Nat.beq k (nat_lit 2)))
  (nat_lit 35322350018580) (Nat.beq k (nat_lit 1)))
  (nat_lit 8) (Nat.beq k (nat_lit 0))

@[expose] noncomputable def sub (j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 8196) (Nat.beq j (nat_lit 0))

end CFSG.KC.L34Alt

end
