module

public import CFSG.Certificates.Kernel.Bounds.Core3

public section

namespace CFSG.Certificates.KB

@[expose] noncomputable def wCovStepE (F : Nat → Nat) (RW RM N Lh nF : Nat) (st : Nat × Nat) :
    Nat × Nat :=
  Prod.rec (motive := fun _ => Nat × Nat) (fun rest x =>
    Bool.rec (Prod.mk (nat_lit 0) bad)
      (Prod.mk (Nat.shiftRight rest (Nat.mul RW Lh)) (Nat.succ x))
      (Nat.rec (motive := fun _ => Bool) true
        (fun c acc => Bool.rec false acc
          (wCovEntry F N nF x (Nat.shiftLeft c (nat_lit 1))
            (Nat.land (Nat.shiftRight rest (Nat.mul RW c)) RM))) Lh)) st

@[expose] noncomputable def wCovElemE (F : Nat → Nat) (RW RM N Lh nF E x : Nat) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun _ x' => x')
    (Nat.rec (motive := fun _ => Nat × Nat) (Prod.mk (Nat.shiftRight E (nat_lit 8)) x)
      (fun _ st => wCovStepE F RW RM N Lh nF st) (Nat.land E (nat_lit 255)))

@[expose] noncomputable def wCovListE (F : Nat → Nat) (RW RM N Lh nF : Nat) (l : List Nat)
    (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun E _ ih x => ih (wCovElemE F RW RM N Lh nF E x)) l x

end CFSG.Certificates.KB

end
