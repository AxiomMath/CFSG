module

public import CFSG.Certificates.Kernel.BabyMonster.F2

public section

namespace CFSG.KC.BM

@[expose] noncomputable def SMn (n : Nat) : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 64) n)) (nat_lit 1)) LM

@[expose] noncomputable def mulSn (n : Nat) (Bs : List Nat) (A : Nat) : Nat :=
  (fun S => Nat.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun u ih acc =>
      (fun t SMa SMb => ih (Nat.xor acc
          (List.rec (motive := fun _ => Nat → Nat → Nat → Nat)
            (fun _ a0 a1 => Nat.xor (Nat.shiftRight a0 t) (Nat.shiftRight a1 (Nat.succ t)))
            (fun T _ ih2 Ac a0 a1 => ih2 (Nat.shiftRight Ac (nat_lit 4096))
                (Nat.xor a0 (Nat.mul (Nat.land Ac LM) (Nat.land T SMa)))
                (Nat.xor a1 (Nat.mul (Nat.shiftRight (Nat.land Ac (nat_lit 340282366920938463463374607431768211455))
                  (nat_lit 64)) (Nat.land T SMb))))
            Bs (Nat.shiftRight A (Nat.mul (nat_lit 64) t)) (nat_lit 0) (nat_lit 0))))
        (Nat.add u u) (Nat.shiftLeft S (Nat.add u u)) (Nat.shiftLeft S (Nat.succ (Nat.add u u))))
    (nat_lit 32) (nat_lit 0)) (SMn n)

@[expose] noncomputable def mulWn (n : Nat) (Ws : List (List Nat)) (A : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun A => A)
    (fun Bs _ ih A => forceB (mulSn n Bs A) ih) Ws A

@[expose] noncomputable def rowsSn (n s : Nat) : Nat :=
  (fun r => Bool.rec (motive := fun _ => Nat) (nat_lit 64) r (Nat.ble r (nat_lit 64)))
    (Nat.sub n (Nat.mul (nat_lit 64) s))

@[expose] noncomputable def idSn (n s : Nat) : Nat :=
  Nat.shiftLeft
    (Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 65) (rowsSn n s)))
      (nat_lit 1)) (nat_lit 36893488147419103231))
    (Nat.mul (nat_lit 4096) s)

@[expose] noncomputable def wfMatn (n : Nat) (M : List Nat) : Bool :=
  Nat.beq (List.rec (motive := fun _ => Nat → Nat) (fun s => s)
    (fun T _ ih s => Bool.rec (motive := fun _ => Nat) (nat_lit 100000) (ih (Nat.succ s))
      (Nat.beq (Nat.land T (Nat.mul (SMn n) (Nat.sub (Nat.shiftLeft (nat_lit 1) (rowsSn n s)) (nat_lit 1)))) T))
    M (nat_lit 0)) (nat_lit 69)

@[expose] noncomputable def foldRowsn (n : Nat) (f : Nat → Nat → Nat → Nat) (M : List Nat) (st : Nat) : Nat :=
  (fun S => List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ st => st)
    (fun T _ ih i st =>
      Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ i st => ih i st)
        (fun _ ih2 T i st =>
          forceB (f i (Nat.land T S) st) (fun st' => ih2 (Nat.shiftRight T (nat_lit 1)) (Nat.succ i) st'))
        (nat_lit 64) T i st) M (nat_lit 0) st) (SMn n)

@[expose] noncomputable def shapeOKn (n : Nat) (M : List Nat) (k : Nat) : Bool :=
  notB (Nat.beq (foldRowsn n (fun i r st =>
    Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) st (Nat.beq r (nat_lit 0)))
      (echStep r st) (Nat.blt i k)) M topRow) (nat_lit 0))

@[expose] noncomputable def stripOfBlockn (n : Nat) (blk : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun r _ ih t acc => Bool.rec (motive := fun _ => Nat) (Nat.shiftLeft (nat_lit 1) (nat_lit 282624))
      (forceB (Nat.lor acc (Nat.shiftLeft (spreadRow (Nat.lor r (Nat.mul t (nat_lit 0)))) t))
        (fun acc' => ih (Nat.succ t) acc'))
      (Nat.beq (Nat.shiftRight r n) (nat_lit 0))) blk (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def blockOKn (n : Nat) (blk : List Nat) (T s : Nat) : Bool :=
  andB (Nat.beq (lenL blk) (rowsSn n s)) (Nat.beq (stripOfBlockn n blk) T)

@[expose] noncomputable def xorL (a : List Nat) : List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun _ => List.nil)
    (fun x _ ih b => List.rec (motive := fun _ => List Nat) List.nil (fun y ys _ => List.cons (Nat.xor x y) (ih ys)) b) a

@[expose] noncomputable def xorBlocks (m : Nat) (Bs : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat)
    (Nat.rec (motive := fun _ => List Nat) List.nil (fun _ acc => List.cons (nat_lit 0) acc) m)
    (fun B _ ih => xorL B ih) Bs

@[expose] noncomputable def eqL (a : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun b => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) b)
    (fun x _ ih b => List.rec (motive := fun _ => Bool) false (fun y ys _ => andB (Nat.beq x y) (ih ys)) b) a

@[expose] noncomputable def projRow (p f r : Nat) : Nat :=
  (fun y => Nat.lor (Nat.land y (Nat.sub (Nat.shiftLeft (nat_lit 1) p) (nat_lit 1)))
      (Nat.shiftLeft (Nat.shiftRight y (Nat.succ p)) p))
    (Nat.xor r (Nat.mul (Nat.land (Nat.shiftRight r p) (nat_lit 1)) f))

@[expose] noncomputable def projRows (p f : Nat) (R : List Nat) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun r _ ih i => Bool.rec (motive := fun _ => List Nat) (List.cons (projRow p f r) (ih (Nat.succ i)))
      (ih (Nat.succ i)) (Nat.beq i p)) R

@[expose] noncomputable def consN (x : Nat) (L : List Nat) : List Nat := List.cons x L

@[expose] noncomputable def lastL (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun d => d) (fun x _ ih _ => ih x) L (nat_lit 0)

@[expose] noncomputable def dropLastL (L : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun x xs ih => List.rec (motive := fun _ => List Nat) List.nil (fun _ _ _ => List.cons x ih) xs) L

@[expose] noncomputable def quotBlk (p f s : Nat) (Cb E : List Nat) : Bool :=
  eqL (projRows p f Cb (Nat.mul (nat_lit 64) s)) E

end CFSG.KC.BM

end
