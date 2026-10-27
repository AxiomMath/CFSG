module

public import Init

public section

namespace CFSG.KC.Fi22B

@[expose] def R0 : Nat := nat_lit 8

@[expose] def R1 : Nat := nat_lit 651582350874958761227356402098228

@[expose] def R2 : Nat := nat_lit 3065037850497807041164954017588240258110557323916214360

@[expose] def R3 : Nat := nat_lit 1682522872744795077610054832451195797956449741759241438071219433271311929311936557189495708459354018534461317473833963995135403262987023731728085044691196

@[expose] def R4 : Nat := nat_lit 2535359305043973369995331637296

@[expose] def R5 : Nat := nat_lit 716411503555297379066075332726516849329573960

@[expose] def R6 : Nat := nat_lit 201654958310806033305322177858267873611621724199502444761184

@[expose] def R7 : Nat := nat_lit 46951456510758812194972286093042219939148921311312

@[expose] def R8 : Nat := nat_lit 15976752755550151124305997028288307922669791829064198797603315429021679399962768936276112

@[expose] def R9 : Nat := nat_lit 56759965326076164623005699533911082836406483277603056676999623940426961016

@[expose] def R10 : Nat := nat_lit 70426114330315228119624174312221487815224121626704

@[expose] def R11 : Nat := nat_lit 3719877627573470241265782617586996371971656345336619746298027130836103759663232

@[expose] def R12 : Nat := nat_lit 15976752755550122743030941585567610765939644565762387133033808872847149284717124169765008

@[expose] noncomputable def rel (k : Nat) : Nat :=
  (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (nat_lit 0) R12 (Nat.beq k (nat_lit 12))) R11 (Nat.beq k (nat_lit 11))) R10 (Nat.beq k (nat_lit 10))) R9 (Nat.beq k (nat_lit 9))) R8 (Nat.beq k (nat_lit 8))) R7 (Nat.beq k (nat_lit 7))) R6 (Nat.beq k (nat_lit 6))) R5 (Nat.beq k (nat_lit 5))) R4 (Nat.beq k (nat_lit 4))) R3 (Nat.beq k (nat_lit 3))) R2 (Nat.beq k (nat_lit 2))) R1 (Nat.beq k (nat_lit 1))) R0 (Nat.beq k (nat_lit 0)))

@[expose] def list : List Nat := [R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, R12]

@[expose] def S0 : Nat := nat_lit 4

@[expose] def S1 : Nat := nat_lit 151708338112602787819556

@[expose] def S2 : Nat := nat_lit 227562507168731709317156

@[expose] def S3 : Nat := nat_lit 35185177403412

@[expose] def S4 : Nat := nat_lit 592601706350638014496

@[expose] def S5 : Nat := nat_lit 9942357059710490251230191660

@[expose] def S6 : Nat := nat_lit 2798524887656214534798536519645601692917828

@[expose] noncomputable def sub (j : Nat) : Nat :=
  (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (nat_lit 0) S6 (Nat.beq j (nat_lit 6))) S5 (Nat.beq j (nat_lit 5))) S4 (Nat.beq j (nat_lit 4))) S3 (Nat.beq j (nat_lit 3))) S2 (Nat.beq j (nat_lit 2))) S1 (Nat.beq j (nat_lit 1))) S0 (Nat.beq j (nat_lit 0)))

end CFSG.KC.Fi22B

end
