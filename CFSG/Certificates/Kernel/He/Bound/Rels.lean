module

public import Init

public section

namespace CFSG.KC.HeB

@[expose] def R0 : Nat := nat_lit 8
@[expose] def R1 : Nat := nat_lit 2314885530818453532
@[expose] def R2 : Nat :=
  nat_lit 242837316931611696787552177320489309273130339902573082445942584276815501707500847240
@[expose] def R3 : Nat :=
  nat_lit 200871859052076212851742972605385659222126871796571811352672
@[expose] def R4 : Nat :=
  nat_lit 68619626515344247836734402821153751108130991905203219883023879489462443384145435742906708822855840
@[expose] def R5 : Nat := nat_lit 46768766034768966130698322455972145202314093793360
@[expose] def R6 : Nat :=
  nat_lit 14530551559869914373483821247727298275393995507139618029726508606203336065148

@[expose] noncomputable def rel (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat)
          (Bool.rec (motive := fun _ => Nat)
            (Bool.rec (motive := fun _ => Nat)
              (Bool.rec (motive := fun _ => Nat) (nat_lit 0) R6 (Nat.beq k (nat_lit 6)))
              R5 (Nat.beq k (nat_lit 5)))
            R4 (Nat.beq k (nat_lit 4)))
          R3 (Nat.beq k (nat_lit 3)))
        R2 (Nat.beq k (nat_lit 2)))
      R1 (Nat.beq k (nat_lit 1)))
    R0 (Nat.beq k (nat_lit 0))

@[expose] def list : List Nat := [R0, R1, R2, R3, R4, R5, R6]

@[expose] def S0 : Nat := nat_lit 4
@[expose] def S1 : Nat := nat_lit 9007336696852504

@[expose] noncomputable def sub (j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (nat_lit 0) S1 (Nat.beq j (nat_lit 1)))
    S0 (Nat.beq j (nat_lit 0))

@[expose] noncomputable def subLet (j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 2) (nat_lit 0) (Nat.beq j (nat_lit 0))

end CFSG.KC.HeB

end
