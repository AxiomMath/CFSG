module

public import Init

public section

namespace CFSG.KC.U42Alt

@[expose] noncomputable def rel (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat)
  (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat)
  (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
  (nat_lit 38017613178786925127617152488919892315505765222725739815956966124830996296093695277066857725623533665039429812)
    (Nat.beq k (nat_lit 6)))
  (nat_lit 75447508334604805099972575844006767044400406182403846448293996032132584733318596181272286078350605877775438004)
    (Nat.beq k (nat_lit 5)))
  (nat_lit 16355070817440708117330634953367354343488) (Nat.beq k (nat_lit 4)))
  (nat_lit 3807942247354663038171645739056) (Nat.beq k (nat_lit 3)))
  (nat_lit 713634735554877445372974969816450089707634760) (Nat.beq k (nat_lit 2)))
  (nat_lit 35322350018580) (Nat.beq k (nat_lit 1)))
  (nat_lit 8) (Nat.beq k (nat_lit 0))

@[expose] noncomputable def sub (j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 2097160) (Nat.beq j (nat_lit 0))

end CFSG.KC.U42Alt

end
