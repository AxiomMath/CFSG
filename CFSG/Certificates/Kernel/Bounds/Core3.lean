module

public import CFSG.Certificates.Kernel.Bounds.Core2

public section

namespace CFSG.Certificates.KB

@[expose] def constN (c : Nat) : Nat → Nat := fun _ => c

@[expose] noncomputable def wFactNext (F Wd2 : Nat → Nat) (RW RM nCos nW f rest j : Nat) :
    Nat × Nat :=
  Bool.rec (Prod.mk (nat_lit 0) bad) (vFactNext F RW RM nCos f rest (Wd2 j)) (Nat.ble (Nat.succ j) nW)

@[expose] noncomputable def wFactStep (F Wd2 : Nat → Nat) (RW RM nCos nW : Nat) (st : Nat × Nat) :
    Nat × Nat :=
  Prod.rec (motive := fun _ => Nat × Nat) (fun rest f =>
    wFactNext F Wd2 RW RM nCos nW f rest
      (Nat.land (Nat.shiftRight rest (nat_lit 36)) (nat_lit 65535))) st

@[expose] noncomputable def wElem (F Wd2 : Nat → Nat) (RW RM nCos nW E f : Nat) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun _ f' => f')
    (Nat.rec (motive := fun _ => Nat × Nat) (Prod.mk (Nat.shiftRight E (nat_lit 8)) f)
      (fun _ st => wFactStep F Wd2 RW RM nCos nW st) (Nat.land E (nat_lit 255)))

@[expose] noncomputable def wWalkList (F Wd2 : Nat → Nat) (RW RM nCos nW : Nat) (l : List Nat)
    (f : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun f => f)
    (fun E _ ih f => ih (wElem F Wd2 RW RM nCos nW E f)) l f

@[expose] noncomputable def wCovEntry (F : Nat → Nat) (N nF x c r : Nat) : Bool :=
  Bool.rec false (vCovFact N x c r (F (Nat.shiftRight r (nat_lit 1))))
    (Nat.ble (Nat.succ (Nat.shiftRight r (nat_lit 1))) nF)

@[expose] noncomputable def wCovStep (F : Nat → Nat) (RW RM N L nF : Nat) (st : Nat × Nat) :
    Nat × Nat :=
  Prod.rec (motive := fun _ => Nat × Nat) (fun rest x =>
    Bool.rec (Prod.mk (nat_lit 0) bad)
      (Prod.mk (Nat.shiftRight rest (Nat.mul RW L)) (Nat.succ x))
      (Nat.rec (motive := fun _ => Bool) true
        (fun c acc => Bool.rec false acc
          (wCovEntry F N nF x c (Nat.land (Nat.shiftRight rest (Nat.mul RW c)) RM))) L)) st

@[expose] noncomputable def wCovElem (F : Nat → Nat) (RW RM N L nF E x : Nat) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun _ x' => x')
    (Nat.rec (motive := fun _ => Nat × Nat) (Prod.mk (Nat.shiftRight E (nat_lit 8)) x)
      (fun _ st => wCovStep F RW RM N L nF st) (Nat.land E (nat_lit 255)))

@[expose] noncomputable def wCovList (F : Nat → Nat) (RW RM N L nF : Nat) (l : List Nat)
    (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun E _ ih x => ih (wCovElem F RW RM N L nF E x)) l x

@[expose] noncomputable def invOk (inv L : Nat) : Bool :=
  Bool.rec false
    (Nat.rec (motive := fun _ => Bool) true
      (fun c acc => Bool.rec false acc (Nat.beq (byte inv c) (Nat.xor c (nat_lit 1)))) L)
    (Nat.beq (byte inv L) L)

@[expose] noncomputable def lettersLe (eps wd : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun q acc => Bool.rec false acc (Nat.ble (letter wd q) eps)) (wN wd)

@[expose] noncomputable def wordsOk3 (Wd R S : Nat → Nat) (inv eps n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i acc => Bool.rec false
      (Bool.rec false acc (lettersLe eps (Wd i))) (wordOk R S inv eps (Wd i))) n

@[expose] noncomputable def sCode (amap : Nat) (x : Nat × Bool) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun g b =>
    Bool.rec bad
      (Nat.add (Nat.shiftLeft (Nat.sub (byte amap g) (nat_lit 1)) (nat_lit 1))
        (Bool.rec (nat_lit 1) (nat_lit 0) b))
      (Nat.ble (nat_lit 1) (Nat.mul (byte amap g) (Bool.rec (nat_lit 1) (nat_lit 0)
        (Nat.ble (nat_lit 256) g))))) x

@[expose] noncomputable def sEnc (amap : Nat) (w : List (Nat × Bool)) : Nat × Bool :=
  Prod.rec (motive := fun _ => Nat × Bool) (fun v ok =>
    Prod.rec (motive := fun _ => Nat × Bool) (fun letters n =>
      Prod.mk (Nat.lor n (Nat.shiftLeft letters (nat_lit 24))) ok) v)
    (List.rec (motive := fun _ => (Nat × Nat) × Bool)
      (Prod.mk (Prod.mk (nat_lit 0) (nat_lit 0)) true)
      (fun x _ ih => Prod.rec (motive := fun _ => (Nat × Nat) × Bool) (fun v ok =>
        Prod.rec (motive := fun _ => (Nat × Nat) × Bool) (fun letters n =>
          Prod.mk
            (Prod.mk (Nat.lor (Nat.shiftLeft letters (nat_lit 8)) (sCode amap x)) (Nat.succ n))
            (Bool.rec false ok (Nat.ble (Nat.succ (sCode amap x)) (nat_lit 256)))) v) ih)
      w)

@[expose] noncomputable def relsOk (R : Nat → Nat) (nR amap : Nat) (rels : List (List (Nat × Bool))) :
    Bool :=
  Nat.beq
    (List.rec (motive := fun _ => Nat → Nat) (fun j => j)
      (fun r _ ih j => Prod.rec (motive := fun _ => Nat) (fun e ok =>
        Bool.rec (ih j) (Bool.rec (ih bad) (ih (Nat.succ j)) (Nat.beq (R j) e)) ok)
        (sEnc amap r)) rels (nat_lit 0))
    nR

@[expose] noncomputable def subsOk (S : Nat → Nat) (nS amap : Nat) (subs : List (List (Nat × Bool))) :
    Bool :=
  Nat.beq
    (List.rec (motive := fun _ => Nat → Nat) (fun j => j)
      (fun w _ ih j => Prod.rec (motive := fun _ => Nat) (fun e ok =>
        Bool.rec (ih bad) (Bool.rec (ih bad) (ih (Nat.succ j))
          (Nat.beq (S j) (Nat.lor e (nat_lit 256)))) ok)
        (sEnc amap w)) subs (nat_lit 0))
    nS

@[expose] noncomputable def hasRel (amap e : Nat) (rels : List (List (Nat × Bool))) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun r _ ih => Prod.rec (motive := fun _ => Bool) (fun e' ok =>
      Bool.rec ih (Bool.rec ih true (Nat.beq e' e)) ok) (sEnc amap r)) rels

@[expose] noncomputable def relsIn (R : Nat → Nat) (nR amap : Nat) (rels : List (List (Nat × Bool))) :
    Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun j acc => Bool.rec false acc (hasRel amap (R j) rels)) nR

end CFSG.Certificates.KB

end
