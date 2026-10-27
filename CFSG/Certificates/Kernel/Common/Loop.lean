module

public import Init

macro "fld(" r:term ", " o:term ", " m:term ")" : term =>
  `(Nat.land (Nat.shiftRight $r $o) $m)

macro "bAnd(" a:term ", " b:term ")" : term =>
  `(Bool.rec (motive := fun _ => Bool) false $b $a)

macro "nIf(" c:term ", " t:term ", " e:term ")" : term =>
  `(Bool.rec (motive := fun _ => Nat) $e $t $c)

macro "bIf(" c:term ", " t:term ", " e:term ")" : term =>
  `(Bool.rec (motive := fun _ => Bool) $e $t $c)

public section

namespace CFSG.KC.Loop

@[expose] noncomputable def strictN (y : Nat) (k : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def allBelow (m hi : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun h ih => bAnd(
    Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft h 6) l), ih2)) 64, ih)) hi

@[expose] noncomputable def sumBelow (m hi : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun h ih => Nat.add (
    Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
      Nat.add ((fun i => nIf(Nat.blt i m, f i, 0)) (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64) ih) hi

end CFSG.KC.Loop

end
