module

public import Init

public section

namespace CFSG.KC.HNA

@[expose] def R0 : Nat := nat_lit 16
@[expose] def R1 : Nat := nat_lit 9007200061100056
@[expose] def R2 : Nat := nat_lit 2314885530818453532
@[expose] def R3 : Nat := nat_lit 2545204872476774149764117692464
@[expose] def R4 : Nat := nat_lit 46951453733990811773775855542836167865857794379856
@[expose] def R5 : Nat := nat_lit 70427180595541615738355719992759919750533171118160
@[expose] def R6 : Nat := nat_lit 4210704
@[expose] def R7 : Nat := nat_lit 274883153936
@[expose] def R8 : Nat := nat_lit 1182897499255400837152
@[expose] def R9 : Nat := nat_lit 1430046217427467661751191520076067117480288328
@[expose] def R10 : Nat := nat_lit 8421384
@[expose] def R11 : Nat := nat_lit 549764202512
@[expose] def R12 : Nat := nat_lit 550301085712
@[expose] def R13 : Nat := nat_lit 170476091718138809392739428729885827132
@[expose] def R14 : Nat := nat_lit 105967050055700
@[expose] def R15 : Nat := nat_lit 105965439422484
@[expose] def R16 : Nat := nat_lit 123627418701844
@[expose] def R17 : Nat := nat_lit 139052740624
@[expose] def R18 : Nat := nat_lit 27162749723246616

@[expose] noncomputable def rel (k : Nat) : Nat :=
  (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (nat_lit 0) R18 (Nat.beq k (nat_lit 18))) R17 (Nat.beq k (nat_lit 17))) R16 (Nat.beq k (nat_lit 16))) R15 (Nat.beq k (nat_lit 15))) R14 (Nat.beq k (nat_lit 14))) R13 (Nat.beq k (nat_lit 13))) R12 (Nat.beq k (nat_lit 12))) R11 (Nat.beq k (nat_lit 11))) R10 (Nat.beq k (nat_lit 10))) R9 (Nat.beq k (nat_lit 9))) R8 (Nat.beq k (nat_lit 8))) R7 (Nat.beq k (nat_lit 7))) R6 (Nat.beq k (nat_lit 6))) R5 (Nat.beq k (nat_lit 5))) R4 (Nat.beq k (nat_lit 4))) R3 (Nat.beq k (nat_lit 3))) R2 (Nat.beq k (nat_lit 2))) R1 (Nat.beq k (nat_lit 1))) R0 (Nat.beq k (nat_lit 0)))

@[expose] def list : List Nat := [R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, R12, R13, R14, R15, R16, R17, R18]

@[expose] def rels : List (List (Nat × Bool)) := [[(0, true), (0, true), (0, true), (0, true)], [(0, false), (0, false), (1, false), (0, true), (0, true), (1, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true)], [(0, false), (0, false), (0, true), (1, true), (0, true), (1, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (1, false), (1, false)], [(2, true), (2, true), (0, true), (0, true)], [(0, false), (2, false), (0, true), (2, true)], [(1, false), (0, false), (1, false), (2, false), (1, true), (0, true), (1, true), (2, true)], [(1, true), (0, true), (1, true), (1, true), (1, true), (2, true), (1, true), (0, true), (1, true), (1, true), (1, true), (2, true), (1, true), (0, true), (1, true), (1, true), (1, true), (2, true)], [(3, true), (3, true)], [(0, true), (3, true), (0, true), (3, true)], [(1, false), (3, false), (1, true), (3, true)], [(1, true), (2, false), (1, false), (2, false), (3, true), (2, true), (1, true), (2, true), (1, false), (2, true), (3, true), (2, true), (3, true), (2, true), (3, true)], [(4, true), (4, true), (4, true), (4, true), (4, true)], [(0, false), (4, true), (0, true), (4, true), (4, true)], [(2, false), (4, true), (2, true), (4, false), (4, false)], [(4, false), (1, false), (4, true), (1, true)], [(3, true), (4, true), (3, true), (4, true), (3, true), (4, true)]]

@[expose] def CODE : Nat := nat_lit 33167824562596679385344

@[expose] noncomputable def letCode (p : Nat × Bool) : Nat :=
  Prod.rec (motive := fun _ => Nat)
    (fun g b => Nat.land (Nat.shiftRight CODE (Nat.mul (nat_lit 8)
      (Bool.rec (motive := fun _ => Nat) (Nat.succ (Nat.mul (nat_lit 2) g)) (Nat.mul (nat_lit 2) g) b))) (nat_lit 255)) p

@[expose] noncomputable def encW (w : List (Nat × Bool)) : Nat × Nat :=
  List.rec (motive := fun _ => Nat × Nat) (Prod.mk (nat_lit 0) (nat_lit 0))
    (fun x _ ih => Prod.rec (motive := fun _ => Nat × Nat)
      (fun v n => Prod.mk (Nat.lor (letCode x) (Nat.shiftLeft v (nat_lit 8))) (Nat.succ n)) ih) w

@[expose] noncomputable def encEnt (w : List (Nat × Bool)) : Nat :=
  Prod.rec (motive := fun _ => Nat)
    (fun v n => Nat.add (Nat.mul (nat_lit 4) n) (Nat.shiftLeft v (nat_lit 12))) (encW w)

@[expose] noncomputable def eqL (A B : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun B => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) B)
    (fun a _ ih => fun B => List.rec (motive := fun _ => Bool) false
      (fun b tb _ => Bool.rec (motive := fun _ => Bool) false (ih tb) (Nat.beq a b)) B) A B

@[expose] noncomputable def encList (L : List (List (Nat × Bool))) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun h _ ih => List.cons (encEnt h) ih) L

end CFSG.KC.HNA

end
