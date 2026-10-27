module

public import CFSG.Certificates.Kernel.Common.Lce
public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Certificates.Kernel.MonsterConv.Orb

public section

namespace CFSG.KC.MonsterConv.MatChain

open CFSG.KC CFSG.KC.Loop CFSG.KC.MonsterConv.Orb

@[expose] noncomputable def lows (d : Nat) : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul d d)) (nat_lit 1))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) d) (nat_lit 1))

@[expose] noncomputable def mmul (d Lw O A B : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun l acc => Nat.xor acc
      (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A l) Lw) O)
        (Nat.mul (fldW B (Nat.mul d l) d) Lw)))
    d

@[expose] noncomputable def vmul (d v M : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun l acc => Nat.xor acc
      (Nat.mul (fldW v l (nat_lit 1)) (fldW M (Nat.mul d l) d)))
    d

@[expose] noncomputable def ident (d : Nat) : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (Nat.add d (nat_lit 1)) d)) (nat_lit 1))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.add d (nat_lit 1))) (nat_lit 1))

@[expose] noncomputable def invOK (d : Nat) (S Si : Nat → Nat) (m : Nat) : Bool :=
  allBelow m (Nat.add (Nat.shiftRight m (nat_lit 6)) (nat_lit 1))
    (fun s => Nat.beq (mmul d (lows d) (Nat.sub (Nat.shiftLeft (nat_lit 1) d) (nat_lit 1)) (S s) (Si s)) (ident d))

@[expose] noncomputable def wordMat (d : Nat) (S Si : Nat → Nat) (W n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (ident d)
    (fun q acc => strictN acc (fun a =>
      mmul d (lows d) (Nat.sub (Nat.shiftLeft (nat_lit 1) d) (nat_lit 1)) a
        ((fun c => Bool.rec (motive := fun _ => Nat) (S (Nat.shiftRight c (nat_lit 1)))
            (Si (Nat.shiftRight c (nat_lit 1))) (Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 1)))
          (fldW W (Nat.mul (nat_lit 8) q) (nat_lit 8)))))
    n

@[expose] noncomputable def derOK (d : Nat) (S Si DW : Nat → Nat) (m0 m : Nat) : Bool :=
  allBelow m (Nat.add (Nat.shiftRight m (nat_lit 6)) (nat_lit 1)) (fun s =>
    Bool.rec (motive := fun _ => Bool)
      ((fun e => andB
          (Nat.beq (wordMat d S Si (Nat.shiftRight e (nat_lit 16)) (Nat.land e (nat_lit 65535))) (S s))
          (Nat.rec (motive := fun _ => Bool) true
            (fun q acc => andB acc (Nat.blt (Nat.shiftRight (fldW (Nat.shiftRight e (nat_lit 16)) (Nat.mul (nat_lit 8) q) (nat_lit 8)) (nat_lit 1)) s))
            (Nat.land e (nat_lit 65535))))
        (DW s))
      true (Nat.blt s m0))

@[expose] noncomputable def levGensOK (d : Nat) (S bv gl : Nat → Nat) (m L : Nat) : Bool :=
  allBelow L (nat_lit 1) (fun l => allBelow m (Nat.add (Nat.shiftRight m (nat_lit 6)) (nat_lit 1)) (fun s =>
    Bool.rec (motive := fun _ => Bool) true
      (Nat.rec (motive := fun _ => Bool) true (fun k acc => andB acc (Nat.beq (vmul d (bv k) (S s)) (bv k))) l)
      (Nat.blt (nat_lit 0) (Nat.land (gl l) (Nat.shiftLeft (nat_lit 1) s)))))

@[expose] noncomputable def treeOK (d : Nat) (S bv gl : Nat → Nat) (blk tm : Nat → Nat → Nat)
    (F n l lo c : Nat) : Bool :=
  andB
    (orbRange (blk l) (fun g y => Bool.rec (motive := fun _ => Nat) (Nat.shiftLeft (nat_lit 1) d)
        (vmul d y (S g)) (Nat.blt (nat_lit 0) (Nat.land (gl l) (Nat.shiftLeft (nat_lit 1) g))))
      F n (bv l) lo c)
    (allBelow c (Nat.add (Nat.shiftRight c (nat_lit 6)) (nat_lit 1)) (fun j =>
      (fun i => (fun vb pb gb db => (fun r => andB
          (Nat.beq (vmul d (bv l) (tm l i)) (fldW r (nat_lit 0) vb))
          (Bool.rec (motive := fun _ => Bool)
            (Nat.beq (mmul d (lows d) (Nat.sub (Nat.shiftLeft (nat_lit 1) d) (nat_lit 1))
              (tm l (fldW r vb pb)) (S (fldW r (Nat.add vb pb) gb))) (tm l i))
            (Nat.beq (tm l i) (ident d))
            (Nat.beq (fldW r (Nat.add (Nat.add vb pb) gb) db) (nat_lit 0))))
        (getRec (blk l) (Nat.add (Nat.add vb pb) (Nat.add gb db)) i))
        (Nat.land F (nat_lit 255)) (Nat.land (Nat.shiftRight F (nat_lit 8)) (nat_lit 255))
        (Nat.land (Nat.shiftRight F (nat_lit 16)) (nat_lit 255)) (Nat.shiftRight F (nat_lit 24)))
      (Nat.add lo j)))

@[expose] noncomputable def resStep (d : Nat) (S gl osz : Nat → Nat) (tm : Nat → Nat → Nat)
    (L ib e : Nat) : Nat :=
  (fun l x s z r =>
    (fun Lw O => (fun len =>
      Bool.rec (motive := fun _ => Nat) (nat_lit 0) len
        (andB (andB (Nat.blt l L) (andB (Nat.blt x (osz l)) (Nat.blt z (osz l))))
          (andB (Nat.blt (nat_lit 0) (Nat.land (gl l) (Nat.shiftLeft (nat_lit 1) s)))
            ((fun ok_rhs => andB (Nat.beq (Nat.land ok_rhs (nat_lit 1)) (nat_lit 1))
                (Nat.beq (Nat.shiftRight ok_rhs (nat_lit 1)) (mmul d Lw O (tm l x) (S s))))
              (Nat.rec (motive := fun _ => Nat) (Nat.add (Nat.shiftLeft (tm l z) (nat_lit 1)) (nat_lit 1))
                (fun k acc => strictN acc (fun a =>
                  (fun lk yk => Bool.rec (motive := fun _ => Nat) (nat_lit 0)
                      (Nat.add (Nat.shiftLeft (mmul d Lw O (tm lk yk) (Nat.shiftRight a (nat_lit 1))) (nat_lit 1))
                        (nat_lit 1))
                      (andB (Nat.beq (Nat.land a (nat_lit 1)) (nat_lit 1))
                        (andB (Nat.blt l lk) (andB (Nat.blt lk L) (Nat.blt yk (osz lk))))))
                    (fldW e (Nat.add (Nat.add (Nat.mul (nat_lit 2) ib) (nat_lit 16)) (Nat.mul (Nat.add ib (nat_lit 4)) k)) (nat_lit 4))
                    (fldW e (Nat.add (Nat.add (Nat.mul (nat_lit 2) ib) (nat_lit 20)) (Nat.mul (Nat.add ib (nat_lit 4)) k)) ib)))
                r)))))
      (Nat.add (Nat.add (Nat.mul (nat_lit 2) ib) (nat_lit 16)) (Nat.mul (Nat.add ib (nat_lit 4)) r)))
    (lows d) (Nat.sub (Nat.shiftLeft (nat_lit 1) d) (nat_lit 1)))
  (fldW e (nat_lit 0) (nat_lit 4)) (fldW e (nat_lit 4) ib) (fldW e (Nat.add ib (nat_lit 4)) (nat_lit 8))
  (fldW e (Nat.add ib (nat_lit 12)) ib) (fldW e (Nat.add (Nat.mul (nat_lit 2) ib) (nat_lit 12)) (nat_lit 4))

@[expose] noncomputable def resKey (ib e : Nat) : Nat :=
  Nat.add (Nat.shiftLeft (fldW e (nat_lit 0) (nat_lit 4)) (nat_lit 32))
    (Nat.add (Nat.shiftLeft (fldW e (nat_lit 4) ib) (nat_lit 8)) (fldW e (Nat.add ib (nat_lit 4)) (nat_lit 8)))

@[expose] noncomputable def resChunk (d : Nat) (S gl osz : Nat → Nat) (tm : Nat → Nat → Nat)
    (L ib C X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ X => X)
    (fun _ ih J X => strictN (resStep d S gl osz tm L ib J) (fun len =>
      Bool.rec (motive := fun _ => Nat) (nat_lit 0)
        (ih (Nat.shiftRight J len)
          (Nat.add (Nat.succ (Nat.land X (nat_lit 4294967295)))
            (Nat.shiftLeft (Nat.succ (resKey ib J)) (nat_lit 32))))
        (andB (Nat.blt (nat_lit 0) len)
          (Nat.blt (Nat.shiftRight X (nat_lit 32)) (Nat.succ (resKey ib J))))))
    (Nat.land C (nat_lit 65535)) (Nat.shiftRight C (nat_lit 16)) X

@[expose] noncomputable def resTotal (gl osz : Nat → Nat) (L : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun l acc => Nat.add acc (Nat.mul (osz l)
      (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun s c => Nat.add c (fldW (gl l) s (nat_lit 1))) (nat_lit 64)))) L

@[expose] noncomputable def runRes (d : Nat) (S gl osz : Nat → Nat) (tm : Nat → Nat → Nat)
    (L ib : Nat) (Cs : List Nat) (X : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun X => X)
    (fun C _ ih X => strictN (Bool.rec (motive := fun _ => Nat) (resChunk d S gl osz tm L ib C X) (nat_lit 0)
      (Nat.beq X (nat_lit 0))) ih) Cs X

@[expose] noncomputable def memOK (d : Nat) (osz : Nat → Nat) (tm : Nat → Nat → Nat) (L ib M e : Nat) : Bool :=
  (fun acc => andB (Nat.beq (Nat.land acc (nat_lit 1)) (nat_lit 1)) (Nat.beq (Nat.shiftRight acc (nat_lit 1)) M))
  (Nat.rec (motive := fun _ => Nat) (Nat.add (Nat.shiftLeft (ident d) (nat_lit 1)) (nat_lit 1))
    (fun k acc => strictN acc (fun a =>
      (fun lk yk => Bool.rec (motive := fun _ => Nat) (nat_lit 0)
          (Nat.add (Nat.shiftLeft (mmul d (lows d) (Nat.sub (Nat.shiftLeft (nat_lit 1) d) (nat_lit 1)) (tm lk yk)
            (Nat.shiftRight a (nat_lit 1))) (nat_lit 1)) (nat_lit 1))
          (andB (Nat.beq (Nat.land a (nat_lit 1)) (nat_lit 1)) (andB (Nat.blt lk L) (Nat.blt yk (osz lk)))))
        (fldW e (Nat.add (nat_lit 4) (Nat.mul (Nat.add ib (nat_lit 4)) k)) (nat_lit 4))
        (fldW e (Nat.add (nat_lit 8) (Nat.mul (Nat.add ib (nat_lit 4)) k)) ib)))
    (fldW e (nat_lit 0) (nat_lit 4)))

end CFSG.KC.MonsterConv.MatChain

end
