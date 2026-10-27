module

public import Init

public section

namespace CFSG.KC.RuB

@[expose] def R0 : Nat := nat_lit 2105352
@[expose] def R1 : Nat := nat_lit 4210696
@[expose] def R2 : Nat := nat_lit 16
@[expose] def R3 : Nat := nat_lit 166156034813001157104264704933494840
@[expose] def R4 : Nat := nat_lit 151115736459028438450212
@[expose] def R5 : Nat := nat_lit 590304888133134602272
@[expose] def R6 : Nat := nat_lit 2310416978391617568
@[expose] def R7 : Nat := nat_lit 93537532058648896519926575243781746158159098019920
@[expose] def R8 : Nat :=
  nat_lit 10830823627177279462720274274369733125836779380629487182750944456015289194602555457399816210336206885075896217942222642094276816
@[expose] def R9 : Nat :=
  nat_lit 944429979405689312703329989723811416275824736447811437750301938863046330049430315551693104999615076981272347062170629255480094273354135121920328205623170149021037625620
@[expose] def R10 : Nat :=
  nat_lit 19239848553822824019225678762341544892549391144973656792766573204098986241618281804508894655928729024849926684856
@[expose] def R11 : Nat :=
  nat_lit 90857615946102555591922259155913021919677366160664043407018767551234807506757354650580817728148884920745315406674259459712093880582368

@[expose] noncomputable def rel (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat)
          (Bool.rec (motive := fun _ => Nat)
            (Bool.rec (motive := fun _ => Nat)
              (Bool.rec (motive := fun _ => Nat)
                (Bool.rec (motive := fun _ => Nat)
                  (Bool.rec (motive := fun _ => Nat)
                    (Bool.rec (motive := fun _ => Nat)
                      (Bool.rec (motive := fun _ => Nat)
                        (Bool.rec (motive := fun _ => Nat) (nat_lit 0) R11 (Nat.beq k (nat_lit 11)))
                        R10 (Nat.beq k (nat_lit 10)))
                      R9 (Nat.beq k (nat_lit 9)))
                    R8 (Nat.beq k (nat_lit 8)))
                  R7 (Nat.beq k (nat_lit 7)))
                R6 (Nat.beq k (nat_lit 6)))
              R5 (Nat.beq k (nat_lit 5)))
            R4 (Nat.beq k (nat_lit 4)))
          R3 (Nat.beq k (nat_lit 3)))
        R2 (Nat.beq k (nat_lit 2)))
      R1 (Nat.beq k (nat_lit 1)))
    R0 (Nat.beq k (nat_lit 0))

@[expose] def list : List Nat := [R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11]

@[expose] def S0 : Nat := nat_lit 4
@[expose] def S1 : Nat := nat_lit 16388

@[expose] noncomputable def sub (j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (nat_lit 0) S1 (Nat.beq j (nat_lit 1)))
    S0 (Nat.beq j (nat_lit 0))

@[expose] noncomputable def subLet (j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 2) (nat_lit 0) (Nat.beq j (nat_lit 0))

end CFSG.KC.RuB

end
