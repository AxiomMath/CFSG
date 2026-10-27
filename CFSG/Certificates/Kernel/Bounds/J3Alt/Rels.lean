module

public import Init

public section

namespace CFSG.KC.J3A

@[expose] def R0 : Nat := nat_lit 8
@[expose] def R1 : Nat := nat_lit 538976268
@[expose] def R2 : Nat := nat_lit 15914708293520294164764073024719051901207176315555068212290559628654072147992925661302928
@[expose] def R3 : Nat := nat_lit 1042978334469659306273604861485094494045724341426915215355235087362646390859548296341417361560
@[expose] def R4 : Nat := nat_lit 440358453606849205833614551250104384463357178223383906653717519143606682908634732592221394705054035947290800
@[expose] def R5 : Nat := nat_lit 440356213862107028021446943442072993853091232220581125269198274107370615957447660306741245365678373563531440
@[expose] def R6 : Nat := nat_lit 123949255041229081758485925198570227924267648302998152563753814553211682084422363812454376179465508657087403855268582260936
@[expose] def R7 : Nat := nat_lit 34888613676033116588421125818474828218393060801065805113744983344705123856991929677503279820522673677611668553810199387273807379157745888

@[expose] noncomputable def rel (k : Nat) : Nat :=
  (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (nat_lit 0) R7 (Nat.beq k (nat_lit 7))) R6 (Nat.beq k (nat_lit 6))) R5 (Nat.beq k (nat_lit 5))) R4 (Nat.beq k (nat_lit 4))) R3 (Nat.beq k (nat_lit 3))) R2 (Nat.beq k (nat_lit 2))) R1 (Nat.beq k (nat_lit 1))) R0 (Nat.beq k (nat_lit 0)))

@[expose] def list : List Nat := [R0, R1, R2, R3, R4, R5, R6, R7]

@[expose] def rels : List (List (Nat × Bool)) := [[(0, true), (0, true)], [(1, true), (1, true), (1, true)], [(0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true)], [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)], [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false)], [(0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false)], [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false)], [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false)]]

@[expose] noncomputable def letCode (p : Nat × Bool) : Nat :=
  Prod.rec (motive := fun _ => Nat)
    (fun g b => Bool.rec (motive := fun _ => Nat) (Nat.succ (Nat.mul (nat_lit 2) g)) (Nat.mul (nat_lit 2) g) b) p

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

end CFSG.KC.J3A

end
