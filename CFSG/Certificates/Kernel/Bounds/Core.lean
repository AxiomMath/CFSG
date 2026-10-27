module

public section

namespace CFSG.Certificates.KB

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec false b a
@[expose] noncomputable def orB (a b : Bool) : Bool := Bool.rec b true a

@[expose] noncomputable def fld (x o m : Nat) : Nat := Nat.land (Nat.shiftRight x o) m
@[expose] noncomputable def byte (w i : Nat) : Nat :=
  Nat.land (Nat.shiftRight w (Nat.shiftLeft i (nat_lit 3))) (nat_lit 255)

@[expose] noncomputable def rX (r : Nat) : Nat := Nat.land r (nat_lit 268435455)
@[expose] noncomputable def rC (r : Nat) : Nat :=
  Nat.land (Nat.shiftRight r (nat_lit 28)) (nat_lit 255)
@[expose] noncomputable def rY (r : Nat) : Nat := Nat.shiftRight r (nat_lit 36)
@[expose] noncomputable def bad : Nat := nat_lit 4611686018427387904

@[expose] noncomputable def wN (w : Nat) : Nat := Nat.land w (nat_lit 255)
@[expose] noncomputable def wKind (w : Nat) : Nat :=
  Nat.land (Nat.shiftRight w (nat_lit 8)) (nat_lit 1)
@[expose] noncomputable def wBase (w : Nat) : Nat :=
  Nat.land (Nat.shiftRight w (nat_lit 9)) (nat_lit 32767)
@[expose] noncomputable def wLetters (w : Nat) : Nat := Nat.shiftRight w (nat_lit 24)
@[expose] noncomputable def letter (w q : Nat) : Nat :=
  Nat.land (Nat.shiftRight w (Nat.add (nat_lit 24) (Nat.shiftLeft q (nat_lit 3)))) (nat_lit 255)

@[expose] noncomputable def fwd (e a cur : Nat) : Nat :=
  Bool.rec bad (rY e) (andB (Nat.beq (rX e) cur) (Nat.beq (rC e) a))
@[expose] noncomputable def bwd (e ai cur : Nat) : Nat :=
  Bool.rec bad (rX e) (andB (Nat.beq (rY e) cur) (Nat.beq (rC e) ai))

@[expose] noncomputable def refStep (F : Nat → Nat) (f r a ai cur : Nat) : Nat :=
  Bool.rec
    (Bool.rec (fwd (F (Nat.shiftRight r (nat_lit 1))) a cur)
      (bwd (F (Nat.shiftRight r (nat_lit 1))) ai cur)
      (Nat.beq (Nat.land r (nat_lit 1)) (nat_lit 1)))
    bad (Nat.ble f (Nat.shiftRight r (nat_lit 1)))

@[expose] noncomputable def wStep (F : Nat → Nat) (inv RW RM f own t wd refs q cur : Nat) :
    Nat :=
  Bool.rec
    (refStep F f (fld refs (Nat.mul RW (Bool.rec (Nat.sub q (nat_lit 1)) q (Nat.ble q t))) RM)
      (letter wd q) (byte inv (letter wd q)) cur)
    (fwd own (letter wd q) cur)
    (Nat.beq q t)

@[expose] noncomputable def walkEnd (F : Nat → Nat) (inv RW RM f own s t wd refs : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) s (fun q cur => wStep F inv RW RM f own t wd refs q cur)
    (wN wd)

@[expose] noncomputable def walkOk (F : Nat → Nat) (inv RW RM nCos f own s t wd refs : Nat) :
    Bool :=
  andB (Nat.ble (Nat.succ s) nCos) (andB (Nat.ble (Nat.succ t) (wN wd))
    (andB (orB (Nat.beq (wKind wd) (nat_lit 0)) (Nat.beq s (nat_lit 0)))
      (Nat.beq (walkEnd F inv RW RM f own s t wd refs) s)))

@[expose] noncomputable def factOk (F Wd : Nat → Nat) (inv RW RM nCos f rest : Nat) : Bool :=
  walkOk F inv RW RM nCos f (F f) (rX rest) (fld rest (nat_lit 28) (nat_lit 255))
    (Wd (fld rest (nat_lit 36) (nat_lit 65535))) (Nat.shiftRight rest (nat_lit 52))

@[expose] noncomputable def factLen (RW wd : Nat) : Nat :=
  Nat.add (nat_lit 52) (Nat.mul RW (Nat.sub (wN wd) (nat_lit 1)))

@[expose] noncomputable def factStep (F Wd : Nat → Nat) (inv RW RM nCos : Nat) (st : Nat × Nat) :
    Nat × Nat :=
  Prod.rec (motive := fun _ => Nat × Nat) (fun rest f =>
    Bool.rec (Prod.mk (nat_lit 0) bad)
      (Prod.mk (Nat.shiftRight rest (factLen RW (Wd (fld rest (nat_lit 36) (nat_lit 65535)))))
        (Nat.succ f))
      (factOk F Wd inv RW RM nCos f rest)) st

@[expose] noncomputable def elemRun (F Wd : Nat → Nat) (inv RW RM nCos E f : Nat) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun _ f' => f')
    (Nat.rec (motive := fun _ => Nat × Nat) (Prod.mk (Nat.shiftRight E (nat_lit 8)) f)
      (fun _ st => factStep F Wd inv RW RM nCos st) (Nat.land E (nat_lit 255)))

@[expose] noncomputable def walkList (F Wd : Nat → Nat) (inv RW RM nCos : Nat) (l : List Nat)
    (f : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun f => f)
    (fun E _ ih f => ih (elemRun F Wd inv RW RM nCos E f)) l f

@[expose] noncomputable def covF (e x c N : Nat) : Bool :=
  andB (Nat.beq (rX e) x) (andB (Nat.beq (rC e) c) (Nat.ble (Nat.succ (rY e)) N))
@[expose] noncomputable def covB (e x ic N : Nat) : Bool :=
  andB (Nat.beq (rY e) x) (andB (Nat.beq (rC e) ic) (Nat.ble (Nat.succ (rX e)) N))

@[expose] noncomputable def covEntry (F : Nat → Nat) (inv N x c r : Nat) : Bool :=
  Bool.rec (covF (F (Nat.shiftRight r (nat_lit 1))) x c N)
    (covB (F (Nat.shiftRight r (nat_lit 1))) x (byte inv c) N)
    (Nat.beq (Nat.land r (nat_lit 1)) (nat_lit 1))

@[expose] noncomputable def covX (F : Nat → Nat) (inv RW RM N L x rec : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun c acc => andB (covEntry F inv N x c (fld rec (Nat.mul RW c) RM)) acc) L

@[expose] noncomputable def covStep (F : Nat → Nat) (inv RW RM N L : Nat) (st : Nat × Nat) :
    Nat × Nat :=
  Prod.rec (motive := fun _ => Nat × Nat) (fun rest x =>
    Bool.rec (Prod.mk (nat_lit 0) bad)
      (Prod.mk (Nat.shiftRight rest (Nat.mul RW L)) (Nat.succ x))
      (covX F inv RW RM N L x rest)) st

@[expose] noncomputable def covElem (F : Nat → Nat) (inv RW RM N L E x : Nat) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun _ x' => x')
    (Nat.rec (motive := fun _ => Nat × Nat) (Prod.mk (Nat.shiftRight E (nat_lit 8)) x)
      (fun _ st => covStep F inv RW RM N L st) (Nat.land E (nat_lit 255)))

@[expose] noncomputable def covList (F : Nat → Nat) (inv RW RM N L : Nat) (l : List Nat)
    (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun E _ ih x => ih (covElem F inv RW RM N L E x)) l x

@[expose] noncomputable def treeOk' (D : Nat → Nat) (L nCos k own : Nat) : Bool :=
  andB (Nat.beq (rY own) k) (andB (Nat.ble (Nat.succ (rC own)) L)
    (andB (Nat.ble (Nat.succ (rX own)) nCos) (Nat.beq (D k) (Nat.succ (D (rX own))))))

@[expose] noncomputable def treeRange (F D : Nat → Nat) (L nCos k0 cnt : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i acc => andB (treeOk' D L nCos (Nat.add k0 (Nat.succ i)) (F (Nat.add k0 i))) acc) cnt

@[expose] noncomputable def strip (eps w n : Nat) : Nat × Nat :=
  Nat.rec (motive := fun _ => Nat × Nat) (Prod.mk (nat_lit 0) (nat_lit 0))
    (fun i acc => Prod.rec (motive := fun _ => Nat × Nat) (fun v m =>
      Bool.rec
        (Prod.mk (Nat.lor v (Nat.shiftLeft (byte w i) (Nat.shiftLeft m (nat_lit 3)))) (Nat.succ m))
        (Prod.mk v m) (Nat.beq (byte w i) eps)) acc) n

@[expose] noncomputable def rot (r n s : Nat) : Nat :=
  Nat.lor (Nat.shiftRight r (Nat.shiftLeft s (nat_lit 3)))
    (Nat.shiftLeft
      (Nat.land r (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.shiftLeft s (nat_lit 3))) (nat_lit 1)))
      (Nat.shiftLeft (Nat.sub n s) (nat_lit 3)))

@[expose] noncomputable def isRot (r n w : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun s acc => orB (Nat.beq (rot r n s) w) acc) n

@[expose] noncomputable def freeRed (inv w n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i stk => Bool.rec (Nat.add (Nat.shiftLeft stk (nat_lit 8)) (Nat.succ (byte w i)))
        (Nat.shiftRight stk (nat_lit 8))
        (andB (Nat.ble (nat_lit 1) stk)
          (Nat.beq (Nat.land stk (nat_lit 255)) (Nat.succ (byte inv (byte w i)))))) n

@[expose] noncomputable def wordOk' (R S : Nat → Nat) (inv wd : Nat) (vm : Nat × Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun v m =>
    Bool.rec
      (orB (Nat.beq (freeRed inv v m) (nat_lit 0))
        (andB (Nat.beq (wN (R (wBase wd))) m) (isRot (wLetters (R (wBase wd))) m v)))
      (andB (Nat.beq (wN (S (wBase wd))) m) (Nat.beq (wLetters (S (wBase wd))) v))
      (Nat.beq (wKind wd) (nat_lit 1))) vm

@[expose] noncomputable def wordOk (R S : Nat → Nat) (inv eps wd : Nat) : Bool :=
  wordOk' R S inv wd (strip eps (wLetters wd) (wN wd))

@[expose] noncomputable def wordsOk (Wd R S : Nat → Nat) (inv eps n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i acc => andB (wordOk R S inv eps (Wd i)) acc) n

end CFSG.Certificates.KB

end
