module

public import CFSG.Certificates.Kernel.Bounds.Core

public section

namespace CFSG.Certificates.KB

@[expose] noncomputable def vFwd (e a cur : Nat) : Nat :=
  Bool.rec bad (Nat.shiftRight e (nat_lit 36))
    (Bool.rec false (Nat.beq (Nat.land (Nat.shiftRight e (nat_lit 28)) (nat_lit 255)) a)
      (Nat.beq (Nat.land e (nat_lit 268435455)) cur))

@[expose] noncomputable def vBwd (e ai cur : Nat) : Nat :=
  Bool.rec bad (Nat.land e (nat_lit 268435455))
    (Bool.rec false (Nat.beq (Nat.land (Nat.shiftRight e (nat_lit 28)) (nat_lit 255)) ai)
      (Nat.beq (Nat.shiftRight e (nat_lit 36)) cur))

@[expose] noncomputable def vRef (F : Nat → Nat) (f r p cur : Nat) : Nat :=
  Bool.rec
    (Bool.rec (vFwd (F (Nat.shiftRight r (nat_lit 1))) (Nat.land p (nat_lit 255)) cur)
      (vBwd (F (Nat.shiftRight r (nat_lit 1))) (Nat.shiftRight p (nat_lit 8)) cur)
      (Nat.beq (Nat.land r (nat_lit 1)) (nat_lit 1)))
    bad (Nat.ble f (Nat.shiftRight r (nat_lit 1)))

@[expose] noncomputable def vStep (F : Nat → Nat) (RW RM f own t wd refs q cur : Nat) : Nat :=
  Bool.rec
    (vRef F f (Nat.land (Nat.shiftRight refs (Nat.mul RW q)) RM)
      (Nat.land (Nat.shiftRight wd (Nat.add (nat_lit 24) (Nat.shiftLeft q (nat_lit 4))))
        (nat_lit 65535)) cur)
    (vFwd own (Nat.land (Nat.shiftRight wd (Nat.add (nat_lit 24) (Nat.shiftLeft q (nat_lit 4))))
      (nat_lit 255)) cur)
    (Nat.beq q t)

@[expose] noncomputable def vWalkOk (F : Nat → Nat) (RW RM nCos f own s t wd refs : Nat) : Bool :=
  Bool.rec false
    (Bool.rec false
      (Bool.rec (Nat.beq s (nat_lit 0)) true
        (Nat.beq (Nat.land (Nat.shiftRight wd (nat_lit 8)) (nat_lit 1)) (nat_lit 0)))
      (Nat.beq
        (Nat.rec (motive := fun _ => Nat) s (fun q cur => vStep F RW RM f own t wd refs q cur)
          (Nat.land wd (nat_lit 255))) s))
    (Bool.rec false (Nat.ble (Nat.succ t) (Nat.land wd (nat_lit 255)))
      (Nat.ble (Nat.succ s) nCos))

@[expose] noncomputable def vFactNext (F : Nat → Nat) (RW RM nCos f rest wd : Nat) : Nat × Nat :=
  Bool.rec (Prod.mk (nat_lit 0) bad)
    (Prod.mk (Nat.shiftRight rest (Nat.add (nat_lit 52) (Nat.mul RW (Nat.land wd (nat_lit 255)))))
      (Nat.succ f))
    (vWalkOk F RW RM nCos f (F f) (Nat.land rest (nat_lit 268435455))
      (Nat.land (Nat.shiftRight rest (nat_lit 28)) (nat_lit 255)) wd
      (Nat.shiftRight rest (nat_lit 52)))

@[expose] noncomputable def vFactStep (F Wd : Nat → Nat) (RW RM nCos : Nat) (st : Nat × Nat) :
    Nat × Nat :=
  Prod.rec (motive := fun _ => Nat × Nat) (fun rest f =>
    vFactNext F RW RM nCos f rest
      (Wd (Nat.land (Nat.shiftRight rest (nat_lit 36)) (nat_lit 65535)))) st

@[expose] noncomputable def vElem (F Wd : Nat → Nat) (RW RM nCos E f : Nat) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun _ f' => f')
    (Nat.rec (motive := fun _ => Nat × Nat) (Prod.mk (Nat.shiftRight E (nat_lit 8)) f)
      (fun _ st => vFactStep F Wd RW RM nCos st) (Nat.land E (nat_lit 255)))

@[expose] noncomputable def vWalkList (F Wd : Nat → Nat) (RW RM nCos : Nat) (l : List Nat)
    (f : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun f => f)
    (fun E _ ih f => ih (vElem F Wd RW RM nCos E f)) l f

@[expose] noncomputable def vCovFact (N x c r e : Nat) : Bool :=
  Bool.rec
    (Bool.rec false
      (Bool.rec false (Nat.ble (Nat.succ (Nat.shiftRight e (nat_lit 36))) N)
        (Nat.beq (Nat.land (Nat.shiftRight e (nat_lit 28)) (nat_lit 255)) c))
      (Nat.beq (Nat.land e (nat_lit 268435455)) x))
    (Bool.rec false
      (Bool.rec false (Nat.ble (Nat.succ (Nat.land e (nat_lit 268435455))) N)
        (Nat.beq (Nat.land (Nat.shiftRight e (nat_lit 28)) (nat_lit 255)) (Nat.xor c (nat_lit 1))))
      (Nat.beq (Nat.shiftRight e (nat_lit 36)) x))
    (Nat.beq (Nat.land r (nat_lit 1)) (nat_lit 1))

@[expose] noncomputable def vCovEntry (F : Nat → Nat) (N x c r : Nat) : Bool :=
  vCovFact N x c r (F (Nat.shiftRight r (nat_lit 1)))

@[expose] noncomputable def vCovStep (F : Nat → Nat) (RW RM N L : Nat) (st : Nat × Nat) :
    Nat × Nat :=
  Prod.rec (motive := fun _ => Nat × Nat) (fun rest x =>
    Bool.rec (Prod.mk (nat_lit 0) bad)
      (Prod.mk (Nat.shiftRight rest (Nat.mul RW L)) (Nat.succ x))
      (Nat.rec (motive := fun _ => Bool) true
        (fun c acc => Bool.rec false acc
          (vCovEntry F N x c (Nat.land (Nat.shiftRight rest (Nat.mul RW c)) RM))) L)) st

@[expose] noncomputable def vCovElem (F : Nat → Nat) (RW RM N L E x : Nat) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun _ x' => x')
    (Nat.rec (motive := fun _ => Nat × Nat) (Prod.mk (Nat.shiftRight E (nat_lit 8)) x)
      (fun _ st => vCovStep F RW RM N L st) (Nat.land E (nat_lit 255)))

@[expose] noncomputable def vCovList (F : Nat → Nat) (RW RM N L : Nat) (l : List Nat) (x : Nat) :
    Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun E _ ih x => ih (vCovElem F RW RM N L E x)) l x

@[expose] noncomputable def pairs (inv w : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (Nat.land w (nat_lit 16777215))
    (fun q acc => Nat.lor acc (Nat.shiftLeft
      (Nat.lor (letter w q) (Nat.shiftLeft (byte inv (letter w q)) (nat_lit 8)))
      (Nat.add (nat_lit 24) (Nat.shiftLeft q (nat_lit 4))))) (wN w)

@[expose] noncomputable def words2Ok (Wd Wd2 : Nat → Nat) (inv n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun j acc => Bool.rec false acc (Nat.beq (Wd2 j) (pairs inv (Wd j)))) n

end CFSG.Certificates.KB

end
