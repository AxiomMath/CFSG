module

public section

namespace CFSG.KM24

@[expose] noncomputable def mAnd (a b : Bool) : Bool := Bool.rec false b a
@[expose] noncomputable def mOr (a b : Bool) : Bool := Bool.rec b true a

@[expose] noncomputable def lmask (n : Nat) : Nat :=
  Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 16) n)) (nat_lit 1)

@[expose] noncomputable def lt (w i : Nat) : Nat :=
  Nat.land (Nat.shiftRight w (Nat.mul (nat_lit 16) i)) (nat_lit 65535)

@[expose] noncomputable def pk (w n : Nat) : Nat := Nat.lor n (Nat.shiftLeft w (nat_lit 16))
@[expose] noncomputable def pw (x : Nat) : Nat := Nat.shiftRight x (nat_lit 16)
@[expose] noncomputable def pn (x : Nat) : Nat := Nat.land x (nat_lit 65535)

@[expose] noncomputable def push (a m c : Nat) : Nat × Nat :=
  Prod.mk (Nat.lor a (Nat.shiftLeft c (Nat.mul (nat_lit 16) m))) (Nat.succ m)

@[expose] noncomputable def freeRed (w n : Nat) : Nat × Nat :=
  Nat.rec (motive := fun _ => Nat × Nat) (Prod.mk (nat_lit 0) (nat_lit 0))
    (fun i acc => Prod.rec (motive := fun _ => Nat × Nat) (fun a m =>
      Bool.rec (push a m (lt w i))
        (Prod.mk (Nat.land a (lmask (Nat.sub m (nat_lit 1)))) (Nat.sub m (nat_lit 1)))
        (mAnd (Nat.blt (nat_lit 0) m)
          (Nat.beq (lt a (Nat.sub m (nat_lit 1))) (Nat.xor (lt w i) (nat_lit 1))))) acc) n

@[expose] noncomputable def cycRed (p : Nat × Nat) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun w0 n0 =>
    Prod.rec (motive := fun _ => Nat) pk
    (Nat.rec (motive := fun _ => Nat × Nat) (Prod.mk w0 n0)
      (fun _ acc => Prod.rec (motive := fun _ => Nat × Nat) (fun w n =>
        Bool.rec (Prod.mk w n)
          (Prod.mk (Nat.land (Nat.shiftRight w (nat_lit 16)) (lmask (Nat.sub n (nat_lit 2))))
            (Nat.sub n (nat_lit 2)))
          (mAnd (Nat.blt (nat_lit 1) n)
            (Nat.beq (lt w (nat_lit 0)) (Nat.xor (lt w (Nat.sub n (nat_lit 1))) (nat_lit 1))))) acc)
      (Nat.shiftRight n0 (nat_lit 1)))) p

@[expose] noncomputable def red (w n : Nat) : Nat := cycRed (freeRed w n)

@[expose] noncomputable def wInv (w n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (Nat.xor (lt w i) (nat_lit 1))
      (Nat.mul (nat_lit 16) (Nat.sub (Nat.sub n i) (nat_lit 1))))) n

@[expose] noncomputable def rot (w n a : Nat) : Nat :=
  Nat.lor (Nat.shiftRight w (Nat.mul (nat_lit 16) a))
    (Nat.shiftLeft (Nat.land w (lmask a)) (Nat.mul (nat_lit 16) (Nat.sub n a)))

@[expose] noncomputable def subst (w n g s si ns : Nat) : Nat :=
  Prod.rec (motive := fun _ => Nat) red
    (Nat.rec (motive := fun _ => Nat × Nat) (Prod.mk (nat_lit 0) (nat_lit 0))
      (fun i acc => Prod.rec (motive := fun _ => Nat × Nat) (fun a m =>
        Bool.rec (push a m (lt w i))
          (Prod.mk (Nat.lor a (Nat.shiftLeft
              (Bool.rec s si (Nat.beq (Nat.land (lt w i) (nat_lit 1)) (nat_lit 1)))
              (Nat.mul (nat_lit 16) m))) (Nat.add m ns))
          (Nat.beq (Nat.shiftRight (lt w i) (nat_lit 1)) g)) acc) n)

@[expose] noncomputable def occ (w n g : Nat) : Nat × Nat :=
  Nat.rec (motive := fun _ => Nat × Nat) (Prod.mk (nat_lit 0) (nat_lit 0))
    (fun i acc => Prod.rec (motive := fun _ => Nat × Nat) (fun c p =>
      Bool.rec (Prod.mk c p) (Prod.mk (Nat.succ c) i)
        (Nat.beq (Nat.shiftRight (lt w i) (nat_lit 1)) g)) acc) n

@[expose] noncomputable def solveAt (w n p : Nat) : Nat × Nat :=
  Prod.rec (motive := fun _ => Nat × Nat) (fun s ns =>
    Bool.rec (Prod.mk s ns) (Prod.mk (wInv s ns) ns)
      (Nat.beq (Nat.land (lt w p) (nat_lit 1)) (nat_lit 1)))
    (freeRed (Nat.lor (wInv (Nat.land w (lmask p)) p)
        (Nat.shiftLeft (wInv (Nat.shiftRight w (Nat.mul (nat_lit 16) (Nat.succ p)))
          (Nat.sub (Nat.sub n p) (nat_lit 1))) (Nat.mul (nat_lit 16) p)))
      (Nat.sub n (nat_lit 1)))

@[expose] noncomputable def getR (L : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun h _ ih => fun j => Nat.rec (motive := fun _ => Nat) h (fun j' _ => ih j') j) L i

@[expose] noncomputable def setR (L : List Nat) (i x : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun h t ih => fun j => Nat.rec (motive := fun _ => List Nat) (List.cons x t)
      (fun j' _ => List.cons h (ih j')) j) L i

@[expose] noncomputable def mapSubst (L : List Nat) (g s si ns : Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun h _ ih => List.cons (subst (pw h) (pn h) g s si ns) ih) L

@[expose] noncomputable def appR (A B : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) B (fun h _ ih => List.cons h ih) A

@[expose] noncomputable def eqRL (A B : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun B => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) B)
    (fun ha _ ih => fun B => List.rec (motive := fun _ => Bool) false
      (fun hb tb _ => mAnd (Nat.beq ha hb) (ih tb)) B) A B

@[expose] noncomputable def lenR (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def fld (r o : Nat) : Nat := Nat.land (Nat.shiftRight r o) (nat_lit 65535)

@[expose] noncomputable def live (G g : Nat) : Bool :=
  Nat.blt (nat_lit 0) (Nat.land G (Nat.shiftLeft (nat_lit 1) g))

@[expose] noncomputable def stepS (ok : Bool) (L : List Nat) (G g i : Nat) : Bool × (List Nat × Nat) :=
  Prod.rec (motive := fun _ => Bool × (List Nat × Nat)) (fun c p =>
    Prod.rec (motive := fun _ => Bool × (List Nat × Nat)) (fun s ns =>
      Prod.mk (mAnd ok (mAnd (live G g) (Nat.beq c (nat_lit 1))))
        (Prod.mk (mapSubst L g s (wInv s ns) ns) (Nat.sub G (Nat.shiftLeft (nat_lit 1) g))))
      (solveAt (pw (getR L i)) (pn (getR L i)) p))
    (occ (pw (getR L i)) (pn (getR L i)) g)

@[expose] noncomputable def stepC (ok : Bool) (L : List Nat) (G j i a b inv : Nat) : Bool × (List Nat × Nat) :=
  Prod.mk ok (Prod.mk (setR L j (red
    (Nat.lor (Bool.rec (rot (pw (getR L i)) (pn (getR L i)) b)
        (wInv (rot (pw (getR L i)) (pn (getR L i)) b) (pn (getR L i))) (Nat.beq inv (nat_lit 1)))
      (Nat.shiftLeft (rot (pw (getR L j)) (pn (getR L j)) a) (Nat.mul (nat_lit 16) (pn (getR L i)))))
    (Nat.add (pn (getR L i)) (pn (getR L j))))) G)

@[expose] noncomputable def step (r : Nat) (s : Bool × (List Nat × Nat)) : Bool × (List Nat × Nat) :=
  Prod.rec (motive := fun _ => Bool × (List Nat × Nat)) (fun ok LG =>
    Prod.rec (motive := fun _ => Bool × (List Nat × Nat)) (fun L G =>
      Bool.rec
        (Bool.rec
          (Bool.rec (Prod.mk false (Prod.mk L G))
            (Prod.mk ok (Prod.mk (setR L (fld r (nat_lit 2)) (nat_lit 0)) G))
            (Nat.beq (Nat.land r (nat_lit 3)) (nat_lit 2)))
          (stepC ok L G (fld r (nat_lit 2)) (fld r (nat_lit 18)) (fld r (nat_lit 34))
            (fld r (nat_lit 50)) (Nat.land (Nat.shiftRight r (nat_lit 66)) (nat_lit 1)))
          (Nat.beq (Nat.land r (nat_lit 3)) (nat_lit 1)))
        (stepS ok L G (fld r (nat_lit 2)) (fld r (nat_lit 18)))
        (Nat.beq (Nat.land r (nat_lit 3)) (nat_lit 0))) LG) s

@[expose] noncomputable def replay (B m : Nat) (s : Bool × (List Nat × Nat)) : Bool × (List Nat × Nat) :=
  Nat.rec (motive := fun _ => Bool × (List Nat × Nat)) s
    (fun k acc => step (Nat.land (Nat.shiftRight B (Nat.mul (nat_lit 72) k))
      (nat_lit 4722366482869645213695)) acc) m

@[expose] noncomputable def chkReplay (Bk m : Nat) (A B : List Nat) (GA GB : Nat) : Bool :=
  mAnd (Nat.blt Bk (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 72) m)))
    (Prod.rec (motive := fun _ => Bool) (fun ok LG =>
      Prod.rec (motive := fun _ => Bool) (fun L G => mAnd ok (mAnd (eqRL L B) (Nat.beq G GB))) LG)
      (replay Bk m (Prod.mk true (Prod.mk A GA))))

@[expose] noncomputable def t8 (T idx : Nat) : Nat :=
  Nat.land (Nat.shiftRight T (Nat.mul (nat_lit 8) idx)) (nat_lit 255)

@[expose] noncomputable def isTree (P c l d : Nat) : Bool :=
  mOr (mAnd (Nat.blt (nat_lit 0) d) (mAnd (Nat.beq (t8 P (Nat.mul (nat_lit 2) d)) c)
        (Nat.beq (t8 P (Nat.succ (Nat.mul (nat_lit 2) d))) l)))
      (mAnd (Nat.blt (nat_lit 0) c) (mAnd (Nat.beq (t8 P (Nat.mul (nat_lit 2) c)) d)
        (Nat.beq (t8 P (Nat.succ (Nat.mul (nat_lit 2) c))) (Nat.xor l (nat_lit 1)))))

@[expose] noncomputable def trace (T P k2 w n c : Nat) : Nat × (Nat × Nat) :=
  Nat.rec (motive := fun _ => Nat × (Nat × Nat)) (Prod.mk c (Prod.mk (nat_lit 0) (nat_lit 0)))
    (fun i acc => Prod.rec (motive := fun _ => Nat × (Nat × Nat)) (fun cur wm =>
      Prod.mk (t8 T (Nat.add (Nat.mul cur k2) (lt w i)))
        (Bool.rec
          (Prod.rec (motive := fun _ => Nat × Nat) (fun a m =>
            push a m (Nat.mul (nat_lit 2) (Nat.add (Nat.mul cur k2) (lt w i)))) wm)
          wm
          (isTree P cur (lt w i) (t8 T (Nat.add (Nat.mul cur k2) (lt w i)))))) acc) n

@[expose] noncomputable def traces (T P k2 nc x : Nat) (acc : Bool × List Nat) : Bool × List Nat :=
  Nat.rec (motive := fun _ => Bool × List Nat) acc
    (fun i s => Prod.rec (motive := fun _ => Bool × List Nat) (fun ok L =>
      Prod.rec (motive := fun _ => Bool × List Nat) (fun e wm =>
        Prod.mk (mAnd ok (Nat.beq e (Nat.sub (Nat.sub nc i) (nat_lit 1))))
          (List.cons (Prod.rec (motive := fun _ => Nat) pk wm) L))
        (trace T P k2 (pw x) (pn x) (Nat.sub (Nat.sub nc i) (nat_lit 1)))) s) nc

@[expose] noncomputable def invWords (k2 : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) List.nil
    (fun i acc => List.cons (pk (Nat.lor (Nat.sub (Nat.sub k2 i) (nat_lit 1))
      (Nat.shiftLeft (Nat.xor (Nat.sub (Nat.sub k2 i) (nat_lit 1)) (nat_lit 1)) (nat_lit 16)))
      (nat_lit 2)) acc) k2

@[expose] noncomputable def allTraces (T P k2 nc : Nat) (R : List Nat) : Bool × List Nat :=
  List.rec (motive := fun _ => Bool × List Nat) (Prod.mk true List.nil)
    (fun h _ ih => Prod.rec (motive := fun _ => Bool × List Nat) (fun ok L =>
      Prod.rec (motive := fun _ => Bool × List Nat) (fun ok' L' => Prod.mk (mAnd ok ok') (appR L' L))
        (traces T P k2 nc h (Prod.mk true List.nil))) ih)
    (appR R (invWords k2))

@[expose] noncomputable def chkTable (T P k2 nc : Nat) : Bool :=
  mAnd (Nat.rec (motive := fun _ => Bool) true
      (fun i acc => mAnd acc (Nat.blt (t8 T i) nc)) (Nat.mul nc k2))
    (Nat.rec (motive := fun _ => Bool) true
      (fun i acc => mAnd acc (mAnd (Nat.blt (t8 P (Nat.mul (nat_lit 2) (Nat.succ i))) (Nat.succ i))
        (mAnd (Nat.blt (t8 P (Nat.succ (Nat.mul (nat_lit 2) (Nat.succ i)))) k2)
          (Nat.beq (t8 T (Nat.add (Nat.mul (t8 P (Nat.mul (nat_lit 2) (Nat.succ i))) k2)
            (t8 P (Nat.succ (Nat.mul (nat_lit 2) (Nat.succ i)))))) (Nat.succ i)))))
      (Nat.sub nc (nat_lit 1)))

@[expose] noncomputable def gens (T P k2 nc : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x acc => Bool.rec (Nat.lor acc (Nat.shiftLeft (nat_lit 1) x)) acc
      (isTree P (Nat.div x k2) (Nat.mod x k2) (t8 T x))) (Nat.mul nc k2)

@[expose] noncomputable def chkInit (T P k2 nc : Nat) (R A : List Nat) (G : Nat) : Bool :=
  mAnd (chkTable T P k2 nc)
    (mAnd (Nat.beq (gens T P k2 nc) G)
      (Prod.rec (motive := fun _ => Bool) (fun ok L => mAnd ok (eqRL L A)) (allTraces T P k2 nc R)))

@[expose] noncomputable def rename (N G w n : Nat) : Bool × Nat :=
  Nat.rec (motive := fun _ => Bool × Nat) (Prod.mk true (nat_lit 0))
    (fun i acc => Prod.rec (motive := fun _ => Bool × Nat) (fun ok a =>
      Prod.mk (mAnd ok (mAnd (live G (Nat.shiftRight (lt w i) (nat_lit 1)))
          (Nat.blt (nat_lit 0) (lt N (Nat.shiftRight (lt w i) (nat_lit 1))))))
        (Nat.lor a (Nat.shiftLeft
          (Nat.add (Nat.mul (nat_lit 2) (Nat.sub (lt N (Nat.shiftRight (lt w i) (nat_lit 1))) (nat_lit 1)))
            (Nat.land (lt w i) (nat_lit 1)))
          (Nat.mul (nat_lit 16) i)))) acc) n

@[expose] noncomputable def chkRen (N G ng kq : Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool)
    (fun ok im => mAnd ok (mAnd (Nat.blt G (Nat.shiftLeft (nat_lit 1) ng))
      (Nat.beq im (Nat.sub (Nat.shiftLeft (nat_lit 1) kq) (nat_lit 1)))))
    (Nat.rec (motive := fun _ => Bool × Nat) (Prod.mk true (nat_lit 0))
      (fun g acc => Prod.rec (motive := fun _ => Bool × Nat) (fun ok im =>
        Bool.rec (Prod.mk ok im)
          (Prod.mk
            (mAnd ok (mAnd (Nat.blt (nat_lit 0) (lt N g)) (mAnd (Nat.ble (lt N g) kq)
              (Nat.beq (Nat.land im (Nat.shiftLeft (nat_lit 1) (Nat.sub (lt N g) (nat_lit 1))))
                (nat_lit 0)))))
            (Nat.lor im (Nat.shiftLeft (nat_lit 1) (Nat.sub (lt N g) (nat_lit 1)))))
          (live G g)) acc) ng)

@[expose] noncomputable def chkNext (N : Nat) (L B : List Nat) (G ng kq : Nat) : Bool :=
  mAnd (chkRen N G ng kq)
  (List.rec (motive := fun _ => List Nat → Bool)
    (fun B => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) B)
    (fun ha _ ih => fun B =>
      Bool.rec
        (List.rec (motive := fun _ => Bool) false (fun hb tb _ =>
          Prod.rec (motive := fun _ => Bool) (fun ok a =>
            mAnd ok (mAnd (Nat.beq (pk a (pn ha)) hb) (ih tb))) (rename N G (pw ha) (pn ha))) B)
        (ih B)
        (Nat.beq (pn ha) (nat_lit 0))) L B)

@[expose] noncomputable def chkByteRel (L : List Nat) (i m k2 v : Nat) : Bool :=
  mAnd (Nat.beq (pn (getR L i)) m)
    (mAnd (Nat.rec (motive := fun _ => Bool) true
        (fun j acc => mAnd acc (Nat.blt (lt (pw (getR L i)) j) k2)) m)
      (Nat.beq v (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun j acc => Nat.lor acc (Nat.shiftLeft (lt (pw (getR L i)) j) (Nat.mul (nat_lit 8) j))) m)))

@[expose] noncomputable def invEnt (k2 out c : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) out (nat_lit 255) (Nat.beq c (nat_lit 255)))
    (Nat.xor c (nat_lit 1)) (Nat.blt c k2)

@[expose] noncomputable def invCanon (k2 out w : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c acc => Nat.lor acc (Nat.shiftLeft (invEnt k2 out c) (Nat.mul w c))) (nat_lit 256)

@[expose] noncomputable def chkInvCanon (INV INV8 k2 : Nat) : Bool :=
  mAnd (Nat.beq INV (invCanon k2 (nat_lit 65535) (nat_lit 16)))
    (Nat.beq INV8 (invCanon k2 (nat_lit 254) (nat_lit 8)))

@[expose] noncomputable def chkInvTab (INV k2 : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun c acc => mAnd acc (Nat.beq (lt INV c) (Nat.xor c (nat_lit 1)))) k2

end CFSG.KM24

end
