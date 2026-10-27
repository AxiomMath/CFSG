module

public import CFSG.Certificates.Kernel.Common.LceS

public section

namespace CFSG.KC.Bind

open CFSG.KC CFSG.KC.LceS

@[expose] noncomputable def allFF : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 2048)) (nat_lit 1)

@[expose] noncomputable def mget (M g : Nat) : Nat := wLet M g

@[expose] noncomputable def mapW (M W n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun q acc => Nat.lor acc
    (Nat.shiftLeft (Nat.add (Nat.mul (nat_lit 2) (mget M (Nat.shiftRight (wLet W q) (nat_lit 1))))
      (Nat.land (wLet W q) (nat_lit 1))) (Nat.mul (nat_lit 8) q))) n

@[expose] noncomputable def mapOK (M W n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun q acc => andB acc
    (Nat.blt (mget M (Nat.shiftRight (wLet W q) (nat_lit 1))) (nat_lit 255))) n

@[expose] noncomputable def subRel (M P C : Nat) : Bool :=
  andB (mapOK M (wWord P) (wLen P)) (andB (Nat.beq (wLen C) (wLen P))
    (Nat.beq (wWord C) (mapW M (wWord P) (wLen P))))

@[expose] noncomputable def mset (M x v : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.sub M (Nat.shiftLeft (Nat.sub (nat_lit 255) v) (Nat.mul (nat_lit 8) x)))
    (andB (Nat.blt (nat_lit 0) M) (andB (Nat.blt v (nat_lit 255)) (andB (Nat.blt x (nat_lit 256))
      (Nat.beq (mget M x) (nat_lit 255)))))

@[expose] noncomputable def stMap (ST : Nat → Nat) (K : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) allFF (fun j acc =>
    Bool.rec (motive := fun _ => Nat) (nat_lit 0) (mset acc (Nat.shiftRight (wWord (ST j)) (nat_lit 1)) j)
      (andB (Nat.beq (wLen (ST j)) (nat_lit 1)) (andB (Nat.beq (Nat.land (wWord (ST j)) (nat_lit 1)) (nat_lit 0))
        (Nat.blt (wWord (ST j)) (nat_lit 256))))) K

@[expose] noncomputable def invMap (Q n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) allFF (fun x acc => mset acc (mget Q x) x) n

@[expose] noncomputable def compMap (A B n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) allFF (fun x acc =>
    Bool.rec (motive := fun _ => Nat) acc (Nat.sub acc (Nat.shiftLeft (Nat.sub (nat_lit 255) (mget A (mget B x))) (Nat.mul (nat_lit 8) x)))
      (Nat.blt (mget B x) (nat_lit 255))) n

@[expose] noncomputable def sqOK (PRT : Nat → Nat) (G Hq : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun g acc => andB acc
    (Nat.beq (PRT (Nat.land (Nat.shiftRight Hq (Nat.mul (nat_lit 16) g)) (nat_lit 65535)))
      (Nat.add (nat_lit 8) (Nat.shiftLeft (Nat.add (Nat.mul (nat_lit 2) g) (Nat.mul (nat_lit 512) g)) (nat_lit 12))))) G

@[expose] noncomputable def kCnt (P : Nat) : Nat := Nat.land P (nat_lit 65535)
@[expose] noncomputable def kStk (P : Nat) : Nat := Nat.shiftRight P (nat_lit 16)
@[expose] noncomputable def mkK (c s : Nat) : Nat := Nat.lor c (Nat.shiftLeft s (nat_lit 16))

@[expose] noncomputable def push (inv P x : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (mkK (Nat.succ (kCnt P)) (Nat.add (Nat.mul (kStk P) (nat_lit 256)) (Nat.succ x)))
    (mkK (Nat.sub (kCnt P) (nat_lit 1)) (Nat.shiftRight (kStk P) (nat_lit 8)))
    (andB (Nat.blt (nat_lit 0) (kCnt P))
      (Nat.beq (Nat.land (kStk P) (nat_lit 255)) (Nat.succ (Nat.xor x inv))))

@[expose] noncomputable def findSub (SB ns g : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun s acc =>
    (fun e => Bool.rec (motive := fun _ => Nat) acc (Nat.succ (Nat.shiftRight e (nat_lit 8)))
      (Nat.beq (Nat.land e (nat_lit 255)) g))
    (Nat.land (Nat.shiftRight SB (Nat.mul (nat_lit 24) s)) (nat_lit 16777215))) ns

@[expose] noncomputable def subsOK (PRT : Nat → Nat) (SB ns : Nat) (inv1 : Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun s acc => andB acc
    ((fun e => (fun R => andB (Nat.blt (nat_lit 0) (wLen R)) (Bool.rec (motive := fun _ => Bool)
        (Nat.beq (Nat.shiftRight (wLet (wWord R) (nat_lit 0)) (nat_lit 1)) (Nat.land e (nat_lit 255)))
        (Nat.beq (wLet (wWord R) (nat_lit 0)) (Nat.add (Nat.mul (nat_lit 2) (Nat.land e (nat_lit 255))) (nat_lit 1)))
        inv1)) (PRT (Nat.shiftRight e (nat_lit 8))))
      (Nat.land (Nat.shiftRight SB (Nat.mul (nat_lit 24) s)) (nat_lit 16777215)))) ns

@[expose] noncomputable def pushTailA (W n P : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun P => P) (fun k ih P =>
    ih (push (nat_lit 0) P (Nat.shiftRight (wLet W (Nat.sub n (Nat.succ k))) (nat_lit 1)))) (Nat.sub n (nat_lit 1)) P

@[expose] noncomputable def stackA (PRT : Nat → Nat) (SB ns W n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun q P =>
    (fun g => (fun s => Bool.rec (motive := fun _ => Nat) (push (nat_lit 0) P g)
        ((fun R => pushTailA (wWord R) (wLen R) P) (PRT (Nat.sub s (nat_lit 1))))
        (Nat.blt (nat_lit 0) s)) (findSub SB ns g))
      (Nat.shiftRight (wLet W q) (nat_lit 1))) n

@[expose] noncomputable def kByte (P i : Nat) : Nat := Nat.land (Nat.shiftRight (kStk P) (Nat.mul (nat_lit 8) i)) (nat_lit 255)

@[expose] noncomputable def cycRed (P : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) P (fun _ P =>
    Bool.rec (motive := fun _ => Nat) P
      (mkK (Nat.sub (kCnt P) (nat_lit 2))
        (Nat.shiftRight (Nat.land (kStk P) (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 8) (Nat.sub (kCnt P) (nat_lit 1)))) (nat_lit 1))) (nat_lit 8)))
      (andB (Nat.ble (nat_lit 2) (kCnt P)) (Nat.beq (kByte P (Nat.sub (kCnt P) (nat_lit 1))) (kByte P (nat_lit 0)))))
    (kCnt P)

@[expose] noncomputable def outW (M mul : Nat) (sgn : Bool) (P : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun q acc =>
    (fun x => Nat.lor acc (Nat.shiftLeft
      (Bool.rec (motive := fun _ => Nat) (Nat.mul mul (mget M x))
        (Nat.add (Nat.mul mul (mget M (Nat.shiftRight x (nat_lit 1)))) (Nat.land x (nat_lit 1))) sgn)
      (Nat.mul (nat_lit 8) q)))
    (Nat.sub (kByte P (Nat.sub (kCnt P) (Nat.succ q))) (nat_lit 1))) (kCnt P)

@[expose] noncomputable def outOK (M : Nat) (sgn : Bool) (P : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun q acc => andB acc
    ((fun x => Nat.blt (mget M (Bool.rec (motive := fun _ => Nat) x (Nat.shiftRight x (nat_lit 1)) sgn)) (nat_lit 255))
      (Nat.sub (kByte P q) (nat_lit 1)))) (kCnt P)

@[expose] noncomputable def derivA (PRT : Nat → Nat) (SB ns M mul P cn cw : Nat) : Bool :=
  letB (cycRed (stackA PRT SB ns (wWord P) (wLen P))) (fun K =>
    andB (outOK M false K) (andB (Nat.beq (kCnt K) cn) (Nat.beq (outW M mul false K) cw)))

@[expose] noncomputable def pushTailF (W n : Nat) (inv : Bool) (P : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun P => P) (fun k ih P =>
    ih (Bool.rec (motive := fun _ => Nat)
      (push (nat_lit 1) P (wLet W (Nat.sub n (Nat.succ k))))
      (push (nat_lit 1) P (Nat.xor (wLet W (Nat.succ k)) (nat_lit 1))) inv)) (Nat.sub n (nat_lit 1)) P

@[expose] noncomputable def stackF (PRT : Nat → Nat) (SB ns W n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun q P =>
    (fun l => (fun s => Bool.rec (motive := fun _ => Nat) (push (nat_lit 1) P l)
        ((fun R => pushTailF (wWord R) (wLen R)
            (Nat.beq (Nat.land (Nat.xor (wLet (wWord R) (nat_lit 0)) l) (nat_lit 1)) (nat_lit 0)) P)
          (PRT (Nat.sub s (nat_lit 1))))
        (Nat.blt (nat_lit 0) s)) (findSub SB ns (Nat.shiftRight l (nat_lit 1))))
      (wLet W q)) n

@[expose] noncomputable def derivF (PRT : Nat → Nat) (SB ns M P C : Nat) : Bool :=
  letB (stackF PRT SB ns (wWord P) (wLen P)) (fun K =>
    andB (outOK M true K) (andB (Nat.beq (kCnt K) (wLen C)) (Nat.beq (outW M (nat_lit 2) true K) (wWord C))))

@[expose] noncomputable def subU (M mul P cn cw : Nat) : Bool :=
  andB (Nat.beq cn (wLen P)) (andB (Nat.beq cw
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun q acc => Nat.lor acc
      (Nat.shiftLeft (Nat.mul mul (mget M (Nat.shiftRight (wLet (wWord P) q) (nat_lit 1)))) (Nat.mul (nat_lit 8) q))) (wLen P)))
    (Nat.rec (motive := fun _ => Bool) true (fun q acc => andB acc
      (andB (Nat.beq (Nat.land (wLet (wWord P) q) (nat_lit 1)) (nat_lit 0))
        (Nat.blt (mget M (Nat.shiftRight (wLet (wWord P) q) (nat_lit 1))) (nat_lit 255)))) (wLen P)))

@[expose] noncomputable def hget (Hs r : Nat) : Nat := Nat.land (Nat.shiftRight Hs (Nat.mul (nat_lit 16) r)) (nat_lit 65535)

@[expose] noncomputable def lceN (RT : Nat → Nat) (r : Nat) : Nat := wLen (RT r)
@[expose] noncomputable def lceW (RT : Nat → Nat) (r : Nat) : Nat := wWord (RT r)
@[expose] noncomputable def dceN (RT : Nat → Nat) (r : Nat) : Nat := Nat.land (RT r) (nat_lit 255)
@[expose] noncomputable def dceW (RT : Nat → Nat) (r : Nat) : Nat := Nat.shiftRight (RT r) (nat_lit 8)

@[expose] noncomputable def relsEq (CRT PRT : Nat → Nat) (R PR Hs : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun r acc => andB acc
    (andB (Nat.blt (hget Hs r) PR) (Nat.beq (CRT r) (PRT (hget Hs r))))) R

@[expose] noncomputable def relsSub (CRT PRT : Nat → Nat) (M R PR Hs : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun r acc => andB acc
    (andB (Nat.blt (hget Hs r) PR) (subRel M (PRT (hget Hs r)) (CRT r)))) R

@[expose] noncomputable def relsA (cn cw PRT : Nat → Nat) (SB ns M mul R PR Hs : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun r acc => andB acc
    (andB (Nat.blt (Nat.land (hget Hs r) (nat_lit 32767)) PR)
      (Bool.rec (motive := fun _ => Bool)
        (subU M mul (PRT (Nat.land (hget Hs r) (nat_lit 32767))) (cn r) (cw r))
        (derivA PRT SB ns M mul (PRT (Nat.land (hget Hs r) (nat_lit 32767))) (cn r) (cw r))
        (Nat.blt (nat_lit 32767) (hget Hs r))))) R

@[expose] noncomputable def relsF (CRT PRT : Nat → Nat) (SB ns M R PR Hs : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun r acc => andB acc
    (andB (Nat.blt (hget Hs r) PR) (derivF PRT SB ns M (PRT (hget Hs r)) (CRT r)))) R

@[expose] noncomputable def levelOK (ST PRT : Nat → Nat) (S Q n K SB ns : Nat) : Bool :=
  letB (invMap Q n) (fun IQ => andB
    (Nat.rec (motive := fun _ => Bool) true (fun c acc => andB acc (Nat.blt (mget S (mget Q c)) (nat_lit 255))) n)
    (Nat.rec (motive := fun _ => Bool) true (fun j acc => andB acc
      ((fun g => orB (Nat.blt (mget IQ g) (nat_lit 255))
        ((fun s => andB (Nat.blt (nat_lit 0) s)
          ((fun R => Nat.rec (motive := fun _ => Bool) true (fun q acc2 => andB acc2
              (Nat.blt (mget IQ (Nat.shiftRight (wLet (wWord R) (Nat.succ q)) (nat_lit 1))) (nat_lit 255)))
            (Nat.sub (wLen R) (nat_lit 1))) (PRT (Nat.sub s (nat_lit 1)))))
          (findSub SB ns g)))
        (Nat.shiftRight (wWord (ST j)) (nat_lit 1)))) K))

@[expose] noncomputable def hintsOK (WT : Nat → Nat) (m R K Hs : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun k ih H => andB
      ((fun w h => Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool) true (Nat.blt h K) (Nat.beq (wKind w) (nat_lit 3)))
          (Nat.blt h R) (Nat.beq (wKind w) (nat_lit 2)))
        (WT (Nat.sub m (Nat.succ k))) (Nat.land H (nat_lit 65535)))
      (ih (Nat.shiftRight H (nat_lit 16)))) m Hs

end CFSG.KC.Bind

end
