module

public import CFSG.Certificates.Kernel.Orders.Mat

public section

namespace CFSG.KC.Ord

open CFSG.KC.Loop

@[expose] noncomputable def regBelow (a r : Nat) : Bool := andB (Nat.blt (nat_lit 0) a) (Nat.blt a r)

@[expose] noncomputable def at16 (L k : Nat) : Nat := bitsN L (Nat.mul (nat_lit 16) k) (nat_lit 16)

@[expose] noncomputable def regsIn (L n r : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih (regBelow (at16 L k) r)) n

@[expose] noncomputable def powR (mul : Nat → Nat → Nat) (ONE M e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ONE
    (fun i acc => strictN acc (fun a =>
      (fun sq => Bool.rec (motive := fun _ => Nat) sq
          (Bool.rec (motive := fun _ => Nat) (mul sq M) M (Nat.beq sq ONE))
          (Nat.beq (Nat.land (Nat.shiftRight e (Nat.sub (nat_lit 15) i)) (nat_lit 1)) (nat_lit 1)))
        (Bool.rec (motive := fun _ => Nat) (mul a a) a (Nat.beq a ONE))))
    (nat_lit 16)

@[expose] noncomputable def insOK (RB : Nat → Nat) (mul : Nat → Nat → Nat) (vld : Nat → Bool)
    (ONE r ins : Nat) : Bool :=
  (fun k a b e => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false
          (andB (regBelow a r) (andB (vld (RB r)) (Nat.beq (mul (RB a) (RB r)) ONE)))
          (Nat.beq k (nat_lit 2)))
        (andB (regBelow a r) (andB (Nat.ble (nat_lit 2) e) (Nat.beq (RB r) (powR mul ONE (RB a) e))))
        (Nat.beq k (nat_lit 1)))
      (andB (regBelow a r) (andB (regBelow b r) (Nat.beq (RB r) (mul (RB a) (RB b)))))
      (Nat.beq k (nat_lit 0)))
    (Nat.land ins (nat_lit 3)) (bitsN ins (nat_lit 2) (nat_lit 16)) (bitsN ins (nat_lit 18) (nat_lit 16))
    (bitsN ins (nat_lit 34) (nat_lit 16))

@[expose] noncomputable def runSlp (RB : Nat → Nat) (mul : Nat → Nat → Nat) (vld : Nat → Bool)
    (ONE : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
            (andB (Nat.blt (nat_lit 0) S) (insOK RB mul vld ONE S (bitsN J (nat_lit 0) (nat_lit 50)))))
          (ih2 (Nat.shiftRight J (nat_lit 50))))
        (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S) ih) Cs

@[expose] noncomputable def rootsOK (RB : Nat → Nat) (vld : Nat → Bool) (lo hi : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => andB ih (Bool.rec (motive := fun _ => Bool) true (vld (RB i)) (Nat.ble lo i))) hi

@[expose] noncomputable def lenL {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def lenRels (l : List (List (Nat × Bool))) : Nat := lenL l

@[expose] noncomputable def nthRel (l : List (List (Nat × Bool))) (k : Nat) : List (Nat × Bool) :=
  List.rec (motive := fun _ => Nat → List (Nat × Bool)) (fun _ => [])
    (fun x _ ih i => Nat.rec (motive := fun _ => List (Nat × Bool)) x (fun j _ => ih j) i) l k

@[expose] noncomputable def relsBounded (rels : List (List (Nat × Bool))) (L : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun r _ ih => andB (List.rec (motive := fun _ => Bool) true
        (fun x _ ih2 => andB (Prod.rec (motive := fun _ => Bool) (fun g _ => Nat.blt g L) x) ih2) r) ih) rels

@[expose] noncomputable def letM (RB : Nat → Nat) (L : Nat) (x : Nat × Bool) : Nat :=
  Prod.rec (motive := fun _ => Nat)
    (fun g s => RB (Bool.rec (motive := fun _ => Nat) (Nat.add (Nat.succ L) g) (Nat.succ g) s)) x

@[expose] noncomputable def segProd (RB : Nat → Nat) (mul : Nat → Nat → Nat) (ONE L lo hi : Nat)
    (l : List (Nat × Bool)) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun x _ ih i acc => strictN (Bool.rec (motive := fun _ => Nat) acc
        ((fun m => Bool.rec (motive := fun _ => Nat) (mul acc m) m (Nat.beq acc ONE)) (letM RB L x))
        (andB (Nat.ble lo i) (Nat.blt i hi))) (ih (Nat.succ i))) l

@[expose] noncomputable def relSegOK (RB : Nat → Nat) (mul : Nat → Nat → Nat)
    (rels : List (List (Nat × Bool))) (ONE L r lo hi Sin Sout : Nat) : Bool :=
  (fun l => andB (Nat.blt r (lenL rels)) (andB (Nat.blt lo hi) (andB (Nat.ble hi (lenL l))
    (Nat.beq (segProd RB mul ONE L lo hi l (nat_lit 0) Sin) Sout))))
  (nthRel rels r)

@[expose] noncomputable def relOK (RB : Nat → Nat) (mul : Nat → Nat → Nat)
    (rels : List (List (Nat × Bool))) (L ONE r : Nat) : Bool :=
  relSegOK RB mul rels ONE L r (nat_lit 0) (lenL (nthRel rels r)) ONE ONE

@[expose] noncomputable def letEq (x y : Nat × Bool) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun g s => Prod.rec (motive := fun _ => Bool)
    (fun h t => andB (Nat.beq g h) (Bool.rec (motive := fun _ => Bool) (notB t) t s)) y) x

@[expose] noncomputable def wordEq (u : List (Nat × Bool)) : List (Nat × Bool) → Bool :=
  List.rec (motive := fun _ => List (Nat × Bool) → Bool)
    (fun v => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) v)
    (fun x _ ih v => List.rec (motive := fun _ => Bool) false (fun y ys _ => andB (letEq x y) (ih ys)) v) u

@[expose] noncomputable def invWord (u : List (Nat × Bool)) : List (Nat × Bool) → List (Nat × Bool) :=
  List.rec (motive := fun _ => List (Nat × Bool) → List (Nat × Bool)) (fun acc => acc)
    (fun x _ ih acc => ih (List.cons (Prod.rec (motive := fun _ => Nat × Bool) (fun g s => (g, notB s)) x) acc)) u

@[expose] noncomputable def relDupOK (rels : List (List (Nat × Bool))) (r s : Nat) : Bool :=
  andB (Nat.blt r s) (andB (Nat.blt s (lenL rels))
    (orB (wordEq (nthRel rels s) (nthRel rels r)) (wordEq (nthRel rels s) (invWord (nthRel rels r) []))))

@[expose] noncomputable def invsOK (RB : Nat → Nat) (mul : Nat → Nat → Nat) (vld : Nat → Bool)
    (L ONE : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun g ih => andB ih
    (andB (vld (RB (Nat.add (Nat.succ L) g))) (Nat.beq (mul (RB (Nat.succ g)) (RB (Nat.add (Nat.succ L) g))) ONE))) L

@[expose] noncomputable def ws (b : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Nat.beq b (nat_lit 32))
    true (andB (Nat.ble (nat_lit 9) b) (Nat.ble b (nat_lit 13)))

@[expose] noncomputable def ent (p b : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.mod (Nat.sub b (nat_lit 48)) p)
    (andB (Nat.ble (nat_lit 48) b) (Nat.ble b (nat_lit 57)))

@[expose] noncomputable def decByte (p d w S RM M St b : Nat) : Nat :=
  nIf(andB (Nat.beq (Nat.land St (nat_lit 1)) (nat_lit 1)) (Nat.blt b (nat_lit 128)),
    nIf(Nat.beq (Nat.land (Nat.shiftRight St (nat_lit 1)) (nat_lit 1)) (nat_lit 1),
      nIf(ws b, St,
        (fun k R => nIf(Nat.blt k (Nat.mul d d),
            (fun j R' => nIf(Nat.beq (Nat.succ j) d,
                nIf(Nat.beq R' (Nat.land (Nat.shiftRight M (Nat.mul S (Nat.div k d))) RM),
                  Nat.add (nat_lit 3) (Nat.shiftLeft (Nat.succ k) (nat_lit 2)),
                  nat_lit 0),
                Nat.add (nat_lit 3) (Nat.add (Nat.shiftLeft (Nat.succ k) (nat_lit 2)) (Nat.shiftLeft R' (nat_lit 26)))))
              (Nat.mod k d) (Nat.lor R (Nat.shiftLeft (ent p b) (Nat.mul w (Nat.mod k d)))),
            St))
          (bitsN St (nat_lit 2) (nat_lit 24)) (Nat.shiftRight St (nat_lit 26))),
      nIf(Nat.beq b (nat_lit 10), Nat.lor St (nat_lit 2), St)),
    nat_lit 0)

@[expose] noncomputable def decRun (F : Nat → Nat) (lb len p d w S RM M : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun St => St)
    (fun leaf _ ih St => strictN (Nat.rec (motive := fun _ => Nat → Nat) (fun St => St)
        (fun q ih2 St => (fun idx => strictN
            (Bool.rec (motive := fun _ => Nat) St
              (decByte p d w S RM M St (Nat.land (Nat.shiftRight (F leaf) (Nat.mul (nat_lit 8) (Nat.sub (Nat.sub lb (nat_lit 1)) q))) (nat_lit 255)))
              (Nat.blt idx len))
            ih2) (Nat.add (Nat.mul leaf lb) (Nat.sub (Nat.sub lb (nat_lit 1)) q)))
        lb St) ih) Cs

@[expose] noncomputable def seedDone (d : Nat) (vld : Nat → Bool) (M St : Nat) : Bool :=
  andB (Nat.beq (Nat.land St (nat_lit 3)) (nat_lit 3))
    (andB (Nat.beq (bitsN St (nat_lit 2) (nat_lit 24)) (Nat.mul d d)) (vld M))

@[expose] noncomputable def pwOK (RB : Nat → Nat) (mul : Nat → Nat → Nat) (PR PW n p nreg : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih
    (andB (Nat.beq (at16 PW (Nat.mul k p)) (at16 PR k))
      (Nat.rec (motive := fun _ => Bool) true (fun e ih2 => andB ih2
        (andB (regBelow (at16 PW (Nat.add (Nat.mul k p) e)) nreg)
          (Bool.rec (motive := fun _ => Bool)
            (Nat.beq (RB (at16 PW (Nat.add (Nat.mul k p) e)))
              (mul (RB (at16 PW (Nat.sub (Nat.add (Nat.mul k p) e) (nat_lit 1)))) (RB (at16 PR k))))
            true (Nat.beq e (nat_lit 0))))) p))) n

@[expose] noncomputable def rhsPc (RB : Nat → Nat) (mul : Nat → Nat → Nat) (ONE PW n p pb x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ONE (fun k acc => (fun e => Bool.rec (motive := fun _ => Nat)
      (mul acc (RB (at16 PW (Nat.sub (Nat.add (Nat.mul k p) e) (nat_lit 1))))) acc (Nat.beq e (nat_lit 0)))
    (bitsN x (Nat.mul pb k) pb)) n

@[expose] noncomputable def pcRelOK (RB : Nat → Nat) (mul : Nat → Nat → Nat) (ONE PR PW n p pb i j x : Nat) : Bool :=
  andB (Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih
      (Bool.rec (motive := fun _ => Bool) (Nat.blt (bitsN x (Nat.mul pb k) pb) p)
        (Nat.beq (bitsN x (Nat.mul pb k) pb) (nat_lit 0)) (Nat.ble k i))) n)
    ((fun R => Bool.rec (motive := fun _ => Bool)
        (Nat.beq (mul (RB (at16 PR j)) (RB (at16 PR i))) (mul (RB (at16 PR i)) R))
        (Nat.beq (RB (at16 PW (Nat.sub (Nat.add (Nat.mul i p) p) (nat_lit 1)))) R)
        (Nat.beq i j))
      (rhsPc RB mul ONE PW n p pb x))

@[expose] noncomputable def runPc (RB : Nat → Nat) (mul : Nat → Nat → Nat) (ONE PR PW n p pb : Nat)
    (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => (fun i j => strictN
            (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
              (Bool.rec (motive := fun _ => Nat) (Nat.add S (nat_lit 256))
                (Bool.rec (motive := fun _ => Nat) (Nat.add (nat_lit 1) n)
                  (Nat.add (nat_lit 1) (Nat.add (Nat.succ i) (Nat.shiftLeft (Nat.succ i) (nat_lit 8)))) (Nat.blt (Nat.succ i) n))
                (Nat.beq (Nat.succ j) n))
              (andB (Nat.blt (nat_lit 0) S) (andB (Nat.blt i n) (andB (Nat.blt j n)
                (pcRelOK RB mul ONE PR PW n p pb i j (bitsN J (nat_lit 0) (Nat.mul n pb)))))))
            (ih2 (Nat.shiftRight J (Nat.mul n pb))))
          (Nat.land (Nat.sub S (nat_lit 1)) (nat_lit 255)) (Nat.shiftRight (Nat.sub S (nat_lit 1)) (nat_lit 8)))
        (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S) ih) Cs

@[expose] noncomputable def runTree (RB PT : Nat → Nat) (vm : Nat → Nat → Nat) (PR fr to : Nat)
    (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => (fun k par g => strictN
            (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
              (andB (Nat.blt (nat_lit 0) S) (andB (Nat.blt par k) (andB (Nat.ble fr g) (andB (Nat.blt g to)
                (Nat.beq (PT k) (vm (PT par) (RB (at16 PR g)))))))))
            (ih2 (Nat.shiftRight J (nat_lit 24))))
          (Nat.sub S (nat_lit 1)) (bitsN J (nat_lit 0) (nat_lit 16)) (bitsN J (nat_lit 16) (nat_lit 8)))
        (Nat.land C (nat_lit 65535)) (Nat.shiftRight C (nat_lit 16)) S) ih) Cs

@[expose] noncomputable def baseFixed (RB : Nat → Nat) (vm : Nat → Nat → Nat) (vldV : Nat → Bool)
    (PR v to n : Nat) : Bool :=
  andB (vldV v) (Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih
    (Bool.rec (motive := fun _ => Bool) true (Nat.beq (vm v (RB (at16 PR k))) v) (Nat.ble to k))) n)

@[expose] noncomputable def sortStep (PT : Nat → Nat) (n S x : Nat) : Nat :=
  (fun bm v => Bool.rec (motive := fun _ => Nat) (nat_lit 0)
      (Nat.add (Nat.succ (Nat.land S (nat_lit 65535))) (Nat.add (Nat.shiftLeft (Nat.lor bm (Nat.shiftLeft (nat_lit 1) x)) (nat_lit 16))
        (Nat.shiftLeft (Nat.succ v) (Nat.add (nat_lit 16) n))))
      (andB (Nat.blt (nat_lit 0) S) (andB (Nat.blt x n) (andB (Nat.beq (Nat.land bm (Nat.shiftLeft (nat_lit 1) x)) (nat_lit 0))
        (Nat.ble (Nat.shiftRight S (Nat.add (nat_lit 16) n)) v)))))
    (Nat.land (Nat.shiftRight S (nat_lit 16)) (Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1))) (PT x)

@[expose] noncomputable def runSorted (PT : Nat → Nat) (n : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => strictN (sortStep PT n S (bitsN J (nat_lit 0) (nat_lit 16))) (ih2 (Nat.shiftRight J (nat_lit 16))))
        (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S) ih) Cs

@[expose] noncomputable def sortedAll (n S : Nat) : Bool :=
  andB (Nat.blt (nat_lit 0) S) (Nat.beq (Nat.land S (nat_lit 65535)) (Nat.succ n))

@[expose] noncomputable def blocksOK (BL nb n : Nat) : Bool :=
  (fun r => andB (Nat.blt (nat_lit 0) r) (Nat.beq (Nat.sub r (nat_lit 1)) n))
    (Nat.rec (motive := fun _ => Nat) (nat_lit 1) (fun b acc => (fun fr to =>
        Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ to)
          (andB (Nat.blt (nat_lit 0) acc) (andB (Nat.beq fr (Nat.sub acc (nat_lit 1))) (Nat.blt fr to))))
      (bitsN BL (Nat.mul (nat_lit 16) b) (nat_lit 8)) (bitsN BL (Nat.add (Nat.mul (nat_lit 16) b) (nat_lit 8)) (nat_lit 8))) nb)

@[expose] noncomputable def upMask (w S d : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft
      (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul w (Nat.sub (Nat.sub d i) (nat_lit 1)))) (nat_lit 1))
      (Nat.add (Nat.mul S i) (Nat.mul w (Nat.succ i))))) d

@[expose] noncomputable def flagOK (mul : Nat → Nat → Nat) (vld : Nat → Bool) (w S d ONE UP Cm Ci : Nat) : Bool :=
  andB (Nat.beq UP (upMask w S d)) (andB (vld Cm) (andB (vld Ci) (Nat.beq (mul Cm Ci) ONE)))

@[expose] noncomputable def uniOK (RB : Nat → Nat) (mul : Nat → Nat → Nat) (w ONE UP Cm Ci PR lo hi : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih (Bool.rec (motive := fun _ => Bool) true
    ((fun M => andB (Nat.beq (Nat.land M UP) (nat_lit 0))
        (Nat.beq (Nat.land M (Nat.mul ONE (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1)))) ONE))
      (mul (mul Cm (RB (at16 PR k))) Ci)) (Nat.ble lo k))) hi

@[expose] noncomputable def primeOK (RB : Nat → Nat) (mul : Nat → Nat → Nat) (ONE nreg r q : Nat) : Bool :=
  andB (regBelow r nreg) (andB (Nat.beq (powR mul ONE (RB r) q) ONE) (notB (Nat.beq (RB r) ONE)))

end CFSG.KC.Ord

end
