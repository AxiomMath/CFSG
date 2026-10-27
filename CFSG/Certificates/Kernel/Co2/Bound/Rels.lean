module

public import Init

public section

namespace CFSG.KC.Co2B

@[expose] def R0 : Nat := nat_lit 8

@[expose] def R1 : Nat := nat_lit 35322350018580

@[expose] def R2 : Nat := nat_lit 3383157571504304891357917998390451414073069945585680283030085697644

@[expose] def R3 : Nat := nat_lit 10889285298773153466024857054791737544768

@[expose] def R4 : Nat := nat_lit 201651911278473377916079870910969176382732993334568784236640

@[expose] def R5 : Nat := nat_lit 200870320593700010505133806019716433877269883680349534294112

@[expose] def R6 : Nat := nat_lit 862731508808081115064885124098705210625091118015054527252495005126768

@[expose] def R7 : Nat := nat_lit 85139946304078962523086085112430824526418055254041011223129347699045830776

@[expose] def R8 : Nat := nat_lit 5579731520984132000527800081179679611388487980572054841108518958022570195030144

@[expose] def R9 : Nat := nat_lit 181857825143591396633774009680271005986356768659778730548869182662499099527212365156917137446804788437929578077119593252883360526985495591753150845534382977176344387911960

@[expose] noncomputable def rel (k : Nat) : Nat :=
  (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (nat_lit 0) R9 (Nat.beq k (nat_lit 9))) R8 (Nat.beq k (nat_lit 8))) R7 (Nat.beq k (nat_lit 7))) R6 (Nat.beq k (nat_lit 6))) R5 (Nat.beq k (nat_lit 5))) R4 (Nat.beq k (nat_lit 4))) R3 (Nat.beq k (nat_lit 3))) R2 (Nat.beq k (nat_lit 2))) R1 (Nat.beq k (nat_lit 1))) R0 (Nat.beq k (nat_lit 0)))

@[expose] def list : List Nat := [R0, R1, R2, R3, R4, R5, R6, R7, R8, R9]

@[expose] def S0 : Nat := nat_lit 4

@[expose] def S1 : Nat := nat_lit 590309338887215910944

@[expose] def S2 : Nat := nat_lit 885452740535659794464

@[expose] def S3 : Nat := nat_lit 2545204948330938702362670272560

@[expose] def S4 : Nat := nat_lit 3817807232863302515056837660720

@[expose] def S5 : Nat := nat_lit 9903671433473814987102232620

@[expose] def S6 : Nat := nat_lit 250203814774394291686806420998594616

@[expose] noncomputable def sub (j : Nat) : Nat :=
  (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (nat_lit 0) S6 (Nat.beq j (nat_lit 6))) S5 (Nat.beq j (nat_lit 5))) S4 (Nat.beq j (nat_lit 4))) S3 (Nat.beq j (nat_lit 3))) S2 (Nat.beq j (nat_lit 2))) S1 (Nat.beq j (nat_lit 1))) S0 (Nat.beq j (nat_lit 0)))

end CFSG.KC.Co2B

end
