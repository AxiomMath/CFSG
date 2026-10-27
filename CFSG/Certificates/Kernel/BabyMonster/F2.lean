module

public import Init

public section

namespace CFSG.KC.BM

@[expose] noncomputable def forceB (v : Nat) (k : Nat → Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (k v) (k v) (Nat.beq v (nat_lit 0))

@[expose] noncomputable def forceBB (v : Nat) (k : Nat → Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (k v) (k v) (Nat.beq v (nat_lit 0))

@[expose] noncomputable def LM : Nat := nat_lit 18446744073709551615

@[expose] noncomputable def SM : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 279680)) (nat_lit 1)) LM

@[expose] noncomputable def mulS (Bs : List Nat) (A : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun u ih acc =>
      (fun t SMa SMb => ih (Nat.xor acc
          (List.rec (motive := fun _ => Nat → Nat → Nat → Nat)
            (fun _ a0 a1 => Nat.xor (Nat.shiftRight a0 t) (Nat.shiftRight a1 (Nat.succ t)))
            (fun T _ ih2 Ac a0 a1 => ih2 (Nat.shiftRight Ac (nat_lit 4096))
                (Nat.xor a0 (Nat.mul (Nat.land Ac LM) (Nat.land T SMa)))
                (Nat.xor a1 (Nat.mul (Nat.shiftRight (Nat.land Ac (nat_lit 340282366920938463463374607431768211455))
                  (nat_lit 64)) (Nat.land T SMb))))
            Bs (Nat.shiftRight A (Nat.mul (nat_lit 64) t)) (nat_lit 0) (nat_lit 0))))
        (Nat.add u u) (Nat.shiftLeft SM (Nat.add u u)) (Nat.shiftLeft SM (Nat.succ (Nat.add u u))))
    (nat_lit 32) (nat_lit 0)

@[expose] noncomputable def mulW (Ws : List (List Nat)) (A : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun A => A)
    (fun Bs _ ih A => forceB (mulS Bs A) ih) Ws A

@[expose] noncomputable def rowsS (s : Nat) : Nat :=
  (fun r => Bool.rec (motive := fun _ => Nat) (nat_lit 64) r (Nat.ble r (nat_lit 64)))
    (Nat.sub (nat_lit 4370) (Nat.mul (nat_lit 64) s))

@[expose] noncomputable def idS (s : Nat) : Nat :=
  Nat.shiftLeft
    (Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 65) (rowsS s)))
      (nat_lit 1)) (nat_lit 36893488147419103231))
    (Nat.mul (nat_lit 4096) s)

@[expose] noncomputable def maskS (s : Nat) : Nat :=
  Nat.mul SM (Nat.sub (Nat.shiftLeft (nat_lit 1) (rowsS s)) (nat_lit 1))

@[expose] noncomputable def wfMat (M : List Nat) : Bool :=
  Nat.beq (List.rec (motive := fun _ => Nat → Nat) (fun s => s)
    (fun T _ ih s => Bool.rec (motive := fun _ => Nat) (nat_lit 100000) (ih (Nat.succ s))
      (Nat.beq (Nat.land T (maskS s)) T)) M (nat_lit 0)) (nat_lit 69)

@[expose] noncomputable def eqMat (X Y : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun Y => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) Y)
    (fun x _ ih Y => List.rec (motive := fun _ => Bool) false
      (fun y ys _ => Bool.rec (motive := fun _ => Bool) false (ih ys) (Nat.beq x y)) Y) X Y

@[expose] noncomputable def isId (X : List Nat) : Bool :=
  Nat.beq (List.rec (motive := fun _ => Nat → Nat) (fun s => s)
    (fun T _ ih s => Bool.rec (motive := fun _ => Nat) (nat_lit 100000) (ih (Nat.succ s))
      (Nat.beq T (idS s))) X (nat_lit 0)) (nat_lit 69)

@[expose] noncomputable def vecMul (Rb : List (List Nat)) (v : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun blk _ ih v acc =>
      List.rec (motive := fun _ => Nat → Nat → Nat) (fun v acc => ih v acc)
        (fun r _ ih2 v acc =>
          forceB (Nat.xor acc (Nat.mul (Nat.land v (nat_lit 1)) r)) (fun acc' =>
            ih2 (Nat.shiftRight v (nat_lit 1)) acc')) blk v acc) Rb v (nat_lit 0)

@[expose] noncomputable def vecW (Ws : List (List (List Nat))) (v : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun v => v)
    (fun R _ ih v => forceB (vecMul R v) ih) Ws v

@[expose] noncomputable def notB (b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false b

@[expose] noncomputable def andB (b c : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false c b

@[expose] noncomputable def foldRows (f : Nat → Nat → Nat → Nat) (M : List Nat) (st : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ st => st)
    (fun T _ ih i st =>
      Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ i st => ih i st)
        (fun _ ih2 T i st =>
          forceB (f i (Nat.land T SM) st) (fun st' => ih2 (Nat.shiftRight T (nat_lit 1)) (Nat.succ i) st'))
        (nat_lit 64) T i st) M (nat_lit 0) st

@[expose] noncomputable def echStep (r st : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0) r
    (andB (notB (Nat.beq r (nat_lit 0))) (andB (Nat.blt r st) (Nat.blt r (Nat.xor r st))))

@[expose] noncomputable def topRow : Nat := Nat.shiftLeft (nat_lit 1) (nat_lit 279681)

@[expose] noncomputable def shapeOK (M : List Nat) (k : Nat) : Bool :=
  notB (Nat.beq (foldRows (fun i r st =>
    Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) st (Nat.beq r (nat_lit 0)))
      (echStep r st) (Nat.blt i k)) M topRow) (nat_lit 0))

@[expose] noncomputable def echFrom (M : List Nat) (k : Nat) : Bool :=
  notB (Nat.beq (foldRows (fun i r st =>
    Bool.rec (motive := fun _ => Nat) st
      (Bool.rec (motive := fun _ => Nat) st (echStep r st) (Nat.blt i (nat_lit 4370)))
      (Nat.ble k i)) M topRow) (nat_lit 0))

@[expose] noncomputable def lowM (m : Nat) : Nat :=
  Nat.mul SM (Nat.sub (Nat.shiftLeft (nat_lit 1) m) (nat_lit 1))

@[expose] noncomputable def rowsBlk (X lo m : Nat) : Nat :=
  Nat.land (Nat.shiftRight X lo) (lowM m)

@[expose] noncomputable def rowOf (X t : Nat) : Nat := Nat.land (Nat.shiftRight X t) SM

@[expose] noncomputable def rowList (Xs : List Nat) (m : Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun X _ ih =>
      Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
        (fun t ih2 acc => ih2 (List.cons (rowOf X (Nat.sub (Nat.sub m t) (nat_lit 1))) acc)) m ih) Xs

@[expose] noncomputable def allDistinct (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x xs ih => andB ih
      (List.rec (motive := fun _ => Bool) true (fun y _ ih2 => andB ih2 (notB (Nat.beq x y))) xs)) L

@[expose] noncomputable def onlyRows (X m : Nat) : Bool := Nat.beq (Nat.land X (lowM m)) X

@[expose] noncomputable def Q63 : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 3969)) (nat_lit 1)) (nat_lit 9223372036854775807)

@[expose] noncomputable def SM63 : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 4032)) (nat_lit 1)) LM

@[expose] noncomputable def spreadRow (r : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun q acc =>
    Nat.lor acc (Nat.shiftLeft
      (Nat.land (Nat.mul (Nat.land (Nat.shiftRight r (Nat.mul (nat_lit 63) q)) (nat_lit 9223372036854775807))
        Q63) SM63) (Nat.mul (nat_lit 4032) q))) (nat_lit 70)

@[expose] noncomputable def lenL (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def lenLL (L : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def stripOfBlock (blk : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun r _ ih t acc => Bool.rec (motive := fun _ => Nat) (Nat.shiftLeft (nat_lit 1) (nat_lit 279680))
      (forceB (Nat.lor acc (Nat.shiftLeft (spreadRow (Nat.lor r (Nat.mul t (nat_lit 0)))) t))
        (fun acc' => ih (Nat.succ t) acc'))
      (Nat.beq (Nat.shiftRight r (nat_lit 4370)) (nat_lit 0))) blk (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def blockOK (blk : List Nat) (T s : Nat) : Bool :=
  andB (Nat.beq (lenL blk) (rowsS s)) (Nat.beq (stripOfBlock blk) T)

end CFSG.KC.BM

end
