module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KLie.CT

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec false b a
@[expose] noncomputable def orB (a b : Bool) : Bool := Bool.rec b true a
@[expose] noncomputable def notB (a : Bool) : Bool := Bool.rec true false a

@[expose] noncomputable def pw2 (w : Nat) : Nat := Nat.shiftLeft (nat_lit 1) w

@[expose] noncomputable def maskN (w : Nat) : Nat := Nat.sub (pw2 w) (nat_lit 1)

@[expose] noncomputable def fget (X i w : Nat) : Nat :=
  Nat.land (Nat.shiftRight X (Nat.mul i w)) (maskN w)

@[expose] noncomputable def bit (X i : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight X i) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def allN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => andB (f i) ih) n

@[expose] noncomputable def anyN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i ih => orB (f i) ih) n

@[expose] noncomputable def orN (n : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun i ih => Nat.lor (f i) ih) n

@[expose] noncomputable def sumN (n : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun i ih => Nat.add (f i) ih) n

@[expose] noncomputable def prodN (n : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 1) (fun i ih => Nat.mul (f i) ih) n

@[expose] noncomputable def maxN (n : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i ih => Bool.rec (motive := fun _ => Nat) ih (f i) (Nat.blt ih (f i))) n

@[expose] noncomputable def popc (w X : Nat) : Nat :=
  sumN w fun i => Nat.land (Nat.shiftRight X i) (nat_lit 1)

@[expose] noncomputable def dvdB (n m : Nat) : Bool :=
  andB (Nat.blt (nat_lit 0) n) (Nat.beq (Nat.mod m n) (nat_lit 0))

@[expose] noncomputable def sl (n : Nat) : Nat :=
  Nat.mul (pw2 n) (Nat.sub (pw2 (Nat.add n n)) (nat_lit 1))

@[expose] noncomputable def v2is (N e : Nat) : Bool :=
  andB (Nat.beq (Nat.land N (maskN e)) (nat_lit 0)) (bit N e)

@[expose] noncomputable def v2s (d : Nat) : Nat :=
  (fun l => Nat.add (Nat.land (Nat.shiftRight l (nat_lit 1)) (nat_lit 1))
      (Nat.add (Nat.mul (nat_lit 2) (Nat.land (Nat.shiftRight l (nat_lit 2)) (nat_lit 1)))
        (Nat.mul (nat_lit 3) (Nat.land (Nat.shiftRight l (nat_lit 3)) (nat_lit 1)))))
    (Nat.sub d (Nat.land d (Nat.sub d (nat_lit 1))))

@[expose] noncomputable def hitMask (eps X N : Nat) : Nat :=
  orN (Nat.succ N) fun n =>
    Bool.rec (motive := fun _ => Nat) (nat_lit 0)
      (orN (Nat.succ n) fun d =>
        Bool.rec (motive := fun _ => Nat) (nat_lit 0) (pw2 (Nat.add (Nat.mul (nat_lit 16) n) d))
          (andB (dvdB d n) (Nat.beq (Nat.mul (Nat.mul eps (sl n)) d) X)))
      (Nat.ble (nat_lit 2) n)

@[expose] noncomputable def lorL (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun a _ ih => Nat.lor a ih) L

@[expose] noncomputable def bitsOf (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun a _ ih => Nat.lor (pw2 a) ih) L

end CFSG.KLie.CT

end
