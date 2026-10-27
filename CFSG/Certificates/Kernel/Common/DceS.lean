module

public import CFSG.Certificates.Kernel.Common.Dce
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.DceS

open CFSG.KC CFSG.KC.Loop

@[expose] noncomputable def letB (v : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) v

@[expose] noncomputable def idP : Nat := nat_lit 18364758544493064720

@[expose] noncomputable def m64 : Nat := nat_lit 18446744073709551615
@[expose] noncomputable def m32 : Nat := nat_lit 4294967295
@[expose] noncomputable def m20 : Nat := nat_lit 1048575
@[expose] noncomputable def m112 : Nat := nat_lit 5192296858534827628530496329220095

@[expose] noncomputable def patch (f : Nat → Nat) (k v : Nat) : Nat → Nat :=
  fun i => Bool.rec (motive := fun _ => Nat) (f i) v (Nat.beq i k)

@[expose] noncomputable def fct (blk : Nat → Nat) (h : Nat) : Nat :=
  strictN (Nat.shiftRight h (nat_lit 8)) (fun k =>
    rget104 (blk k) (Nat.mul (Nat.land h (nat_lit 255)) (nat_lit 104)))

@[expose] noncomputable def hP (H : Nat) : Nat := Nat.land H m64
@[expose] noncomputable def hK (H : Nat) : Nat := Nat.land (Nat.shiftRight H (nat_lit 64)) (nat_lit 3)
@[expose] noncomputable def hA (H : Nat) : Nat := Nat.land (Nat.shiftRight H (nat_lit 66)) (nat_lit 65535)
@[expose] noncomputable def hB (H : Nat) : Nat := Nat.shiftRight H (nat_lit 82)

@[expose] noncomputable def ltN (L : Nat) : Bool := Nat.beq (Nat.shiftRight L (nat_lit 64)) (nat_lit 1)

@[expose] noncomputable def wN (w : Nat) : Nat := Nat.land w (nat_lit 255)
@[expose] noncomputable def wNr (w : Nat) : Nat := Nat.land (Nat.shiftRight w (nat_lit 8)) (nat_lit 255)
@[expose] noncomputable def wW (w : Nat) : Nat := Nat.shiftRight w (nat_lit 16)
@[expose] noncomputable def rN (r : Nat) : Nat := Nat.land r (nat_lit 255)
@[expose] noncomputable def rW (r : Nat) : Nat := Nat.shiftRight r (nat_lit 8)

@[expose] noncomputable def hdrOK (HT LT : Nat → Nat) (NL h : Nat) : Bool :=
  letB (HT h) (fun H =>
    Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (andB (Nat.beq (hK H) (nat_lit 2)) (andB (Nat.blt (hA H) h) (andB (Nat.blt (hB H) h)
          (Nat.beq (hP H) (pmul (hP (HT (hA H))) (hP (HT (hB H))))))))
        (andB (Nat.blt (hA H) NL) (letB (LT (hA H)) (fun L => andB (ltN L) (Nat.beq (hP H) (Nat.land L m64)))))
        (Nat.beq (hK H) (nat_lit 1)))
      (Nat.beq (hP H) idP)
      (Nat.beq (hK H) (nat_lit 0)))

@[expose] noncomputable def letOK (LT : Nat → Nat) (TL c : Nat) : Bool :=
  letB (LT c) (fun L => Bool.rec (motive := fun _ => Bool)
    (andB (ltN L) (isPerm (Nat.land L m64)))
    (Bool.not (ltN L))
    (Nat.beq c TL))

@[expose] noncomputable def invSelfOK (INV INV8 NL : Nat) : Bool :=
  andB (Nat.blt NL (nat_lit 255))
    (andB (Nat.blt INV (Nat.shiftLeft (nat_lit 1) (nat_lit 4096)))
      (andB (Nat.blt INV8 (Nat.shiftLeft (nat_lit 1) (nat_lit 2048)))
        (Nat.rec (motive := fun _ => Bool) true (fun c ih => andB
          (Bool.rec (motive := fun _ => Bool)
            (Bool.rec (motive := fun _ => Bool)
              (andB (Nat.beq (inv16 INV c) (nat_lit 65535)) (Nat.beq (wLet INV8 c) (nat_lit 254)))
              (andB (Nat.beq (inv16 INV c) (nat_lit 255)) (Nat.beq (wLet INV8 c) (nat_lit 255)))
              (Nat.beq c (nat_lit 255)))
            (andB (Nat.beq (inv16 INV c) c) (Nat.beq (wLet INV8 c) c))
            (Nat.blt c NL)) ih) (nat_lit 256))))

@[expose] noncomputable def invRelOK (RT : Nat → Nat) (NL NR IH : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun c ih => andB ih
    (andB (Nat.blt (Nat.land (Nat.shiftRight IH (Nat.mul (nat_lit 16) c)) (nat_lit 65535)) NR)
      (Nat.beq (RT (Nat.land (Nat.shiftRight IH (Nat.mul (nat_lit 16) c)) (nat_lit 65535)))
        (Nat.add (nat_lit 2) (Nat.shiftLeft (Nat.add c (Nat.mul (nat_lit 256) c)) (nat_lit 8)))))) NL

@[expose] noncomputable def refCount (TL W n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun q acc =>
    Bool.rec (motive := fun _ => Nat) acc (Nat.succ acc)
      (orB (Nat.beq (wLet W q) (nat_lit 255)) (Nat.beq (wLet W q) TL))) n

@[expose] noncomputable def lettersD (LT : Nat → Nat) (NL TL W n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun q acc => andB acc
    (orB (Nat.beq (wLet W q) (nat_lit 255)) (orB (Nat.beq (wLet W q) TL)
      (andB (Nat.blt (wLet W q) NL) (ltN (LT (wLet W q))))))) n

@[expose] noncomputable def wordsOK (WT RT LT : Nat → Nat) (INV INV8 NL TL NR m Hs : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun k ih H => andB
      ((fun w r => andB (lettersD LT NL TL (wW w) (wN w))
          (andB (Nat.beq (refCount TL (wW w) (wN w)) (wNr w))
            (andB (Nat.blt (Nat.land H (nat_lit 65535)) NR)
              (wRel INV INV8 (wW w) (wN w) (rW r) (rN r)))))
        (WT (Nat.sub m (Nat.succ k))) (RT (Nat.land H (nat_lit 65535))))
      (ih (Nat.shiftRight H (nat_lit 16)))) m Hs

@[expose] noncomputable def evalN (LT : Nat → Nat) (NL W m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idP (fun q acc =>
    (fun L => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (pmul acc (Nat.land L m64))
      (andB (Nat.blt (wLet W q) NL) (ltN L))) (LT (wLet W q))) m

@[expose] noncomputable def relOK (RT LT : Nat → Nat) (NL TL r : Nat) : Bool :=
  letB (RT r) (fun R => andB (Nat.blt (rW R) (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 8) (rN R))))
    (andB (Nat.rec (motive := fun _ => Bool) true (fun q acc => andB acc (Nat.blt (wLet (rW R) q) NL)) (rN R))
      (orB (Nat.blt (nat_lit 0) (refCount TL (rW R) (rN R)))
        (Nat.beq (evalN LT NL (rW R) (rN R)) idP))))

@[expose] noncomputable def omOK (PBT OMT GT HT : Nat → Nat) (NB NH PB0 j : Nat) : Bool :=
  letB (PBT j) (fun PB => letB (OMT j) (fun OM =>
    andB (pbOK NB idP PB OM) (andB (Nat.beq (pbTag PB) (Nat.succ j))
    (andB (Nat.blt (imgMasks idP PB) (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 16) (Nat.succ NB))))
    (andB (Nat.blt (nat_lit 0) (fld16 OM (nat_lit 0)))
    (andB (Nat.blt (Nat.land OM m112) (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 16) NB)))
    (andB (Nat.blt (GT j) NH) (andB (gOmOK NB PB0 (hP (HT (GT j))) OM)
      (orB (Nat.beq j (nat_lit 0)) (Nat.blt (Nat.land (OMT (Nat.sub j (nat_lit 1))) m112) (Nat.land OM m112)))))))))))

@[expose] noncomputable def constOK (OMT : Nat → Nat) (NB NO I0 BB BASEM NL TL ND ALIVE : Nat) : Bool :=
  andB (Nat.blt (nat_lit 0) NB) (andB (Nat.ble NB (nat_lit 7)) (andB (Nat.blt I0 NO)
    (andB (bbOK NB BB (OMT I0)) (andB (Nat.beq BASEM (Nat.land (OMT I0) m112))
    (andB (Nat.blt TL NL) (andB (Nat.blt ALIVE (Nat.shiftLeft (nat_lit 1) ND)) (bitAt ALIVE (nat_lit 0))))))))

@[expose] noncomputable def sD (st : Nat) : Nat := Nat.land st (nat_lit 16383)
@[expose] noncomputable def sP (st : Nat) : Nat := Nat.land (Nat.shiftRight st (nat_lit 14)) m64
@[expose] noncomputable def sRi (st : Nat) : Nat := Nat.land (Nat.shiftRight st (nat_lit 78)) (nat_lit 255)
@[expose] noncomputable def sOwn (st : Nat) : Nat := Nat.shiftRight st (nat_lit 86)
@[expose] noncomputable def mkW (D P ri own : Nat) : Nat :=
  Nat.lor D (Nat.lor (Nat.shiftLeft P (nat_lit 14)) (Nat.lor (Nat.shiftLeft ri (nat_lit 78)) (Nat.shiftLeft own (nat_lit 86))))

@[expose] noncomputable def refApply (PBT : Nat → Nat) (NB BB c R dir own st : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (mkW (dDp R) (pmul (dP R) (sP st)) (Nat.succ (sRi st)) own)
        (andB (Nat.beq (sD st) (dD R)) (andB (Nat.blt (nat_lit 0) (dJ R))
          (allIn NB BB (imgMasks (sP st) (PBT (Nat.sub (dJ R) (nat_lit 1))))))))
      (strictN (pmul (pinv (dP R)) (sP st)) (fun P =>
        Bool.rec (motive := fun _ => Nat) (nat_lit 0) (mkW (dD R) P (Nat.succ (sRi st)) own)
          (andB (Nat.beq (sD st) (dDp R)) (andB (Nat.blt (nat_lit 0) (dJ R))
            (allIn NB BB (imgMasks P (PBT (Nat.sub (dJ R) (nat_lit 1)))))))))
      (Nat.beq dir (nat_lit 1)))
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (mkW (dDp R) (pmul (dP R) (sP st)) (Nat.succ (sRi st)) own)
        (andB (Nat.beq (sD st) (dD R)) (Nat.beq (dJ R) (nat_lit 0))))
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (mkW (dD R) (pmul (pinv (dP R)) (sP st)) (Nat.succ (sRi st)) own)
        (andB (Nat.beq (sD st) (dDp R)) (Nat.beq (dJ R) (nat_lit 0))))
      (Nat.beq dir (nat_lit 1)))
    (Nat.beq c (nat_lit 255))

@[expose] noncomputable def wStep (blk LT PBT : Nat → Nat) (NL TL NB BB i Ri ft fd J c st : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (strictN (LT c) (fun L => Bool.rec (motive := fun _ => Nat) (nat_lit 0)
      (mkW (sD st) (pmul (sP st) (Nat.land L m64)) (sRi st) (sOwn st))
      (andB (Nat.blt c NL) (ltN L))))
    (Bool.rec (motive := fun _ => Nat)
      (strictN (Nat.land (Nat.shiftRight J (Nat.mul (nat_lit 32) (Nat.sub (sRi st) (sOwn st)))) m32) (fun e =>
        Bool.rec (motive := fun _ => Nat) (nat_lit 0)
          (strictN (fct blk (Nat.shiftRight e (nat_lit 1))) (fun R =>
            refApply PBT NB BB c R (Nat.land e (nat_lit 1)) (sOwn st) st))
          (Nat.blt (Nat.shiftRight e (nat_lit 1)) i)))
      (refApply PBT NB BB c Ri fd (nat_lit 1) st)
      (Nat.beq (sRi st) ft))
    (orB (Nat.beq c (nat_lit 255)) (Nat.beq c TL))

@[expose] noncomputable def walkRun (blk LT PBT : Nat → Nat) (NL TL NB BB i Ri ft fd J W n : Nat) (k : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun st => st)
    (fun k ih st => strictN (wStep blk LT PBT NL TL NB BB i Ri ft fd J (wLet W (Nat.sub n (Nat.succ k))) st)
      (fun s => Bool.rec (motive := fun _ => Nat) (ih s) (nat_lit 0) (Nat.beq s (nat_lit 0)))) k

@[expose] noncomputable def recOK (ND NO R : Nat) : Bool := dRecOK ND NO R

@[expose] noncomputable def hQuot (HT : Nat → Nat) (a b : Nat) : Nat := pmul (pinv (hP (HT a))) (hP (HT b))

@[expose] noncomputable def walkOK (blk LT HT PBT : Nat → Nat) (NL TL NB BB NH ND i R J w : Nat) : Bool :=
  andB (Nat.blt (Nat.land (Nat.shiftRight J (nat_lit 10)) (nat_lit 65535)) NH)
    (andB (Nat.blt (Nat.land (Nat.shiftRight J (nat_lit 26)) (nat_lit 65535)) NH)
    (andB (Nat.blt (Nat.land (Nat.shiftRight J (nat_lit 42)) (nat_lit 65535)) ND)
    (letB (hQuot HT (Nat.land (Nat.shiftRight J (nat_lit 10)) (nat_lit 65535))
        (Nat.land (Nat.shiftRight J (nat_lit 26)) (nat_lit 65535))) (fun P0 =>
      Nat.beq
        (walkRun blk LT PBT NL TL NB BB i R (Nat.land (Nat.shiftRight J (nat_lit 58)) (nat_lit 255))
          (Nat.land (Nat.shiftRight J (nat_lit 66)) (nat_lit 1)) (Nat.shiftRight J (nat_lit 67)) (wW w) (wN w) (wN w)
          (mkW (Nat.land (Nat.shiftRight J (nat_lit 42)) (nat_lit 65535)) P0 (nat_lit 0) (nat_lit 0)))
        (mkW (Nat.land (Nat.shiftRight J (nat_lit 42)) (nat_lit 65535)) P0 (wNr w) (nat_lit 1))))))

@[expose] noncomputable def sI (S : Nat) : Nat := Nat.land S m32
@[expose] noncomputable def sN (S : Nat) : Nat := Nat.shiftRight S (nat_lit 32)
@[expose] noncomputable def mkS (i nx : Nat) : Nat := Nat.lor i (Nat.shiftLeft nx (nat_lit 32))

@[expose] noncomputable def factStep (blk LT HT PBT : Nat → Nat) (NL TL NB BB NH ND NO J S R w : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0)
    (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat)
          (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (mkS (Nat.succ (sI S)) (sN S))
            (andB (Nat.beq (Nat.land J (nat_lit 3)) (nat_lit 2))
              (walkOK blk LT HT PBT NL TL NB BB NH ND (sI S) R J w)))
          (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (mkS (Nat.succ (sI S)) (sN S))
            (andB (Nat.beq (Nat.land R (nat_lit 549755813887)) (nat_lit 0))
              (andB (Nat.blt (Nat.land (Nat.shiftRight J (nat_lit 2)) (nat_lit 65535)) NH)
                (andB (Nat.blt (Nat.land (Nat.shiftRight J (nat_lit 18)) (nat_lit 65535)) NH)
                  (Nat.beq (dP R) (hQuot HT (Nat.land (Nat.shiftRight J (nat_lit 2)) (nat_lit 65535))
                    (Nat.land (Nat.shiftRight J (nat_lit 18)) (nat_lit 65535))))))))
          (Nat.beq (Nat.land J (nat_lit 3)) (nat_lit 1)))
        (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (mkS (Nat.succ (sI S)) (Nat.succ (sN S)))
          (andB (Nat.blt (nat_lit 0) (dJ R)) (andB (Nat.beq (dDp R) (sN S))
            (andB (Nat.blt (dD R) (sN S)) (Nat.beq (dP R) idP)))))
        (Nat.beq (Nat.land J (nat_lit 3)) (nat_lit 0)))
      (recOK ND NO R))
    (Nat.blt (nat_lit 0) S)

@[expose] noncomputable def jLen (J w : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (Nat.add (nat_lit 35) (Nat.mul (nat_lit 32) (wNr w))) (nat_lit 34)
      (Nat.beq (Nat.land J (nat_lit 3)) (nat_lit 1)))
    (nat_lit 2)
    (Nat.beq (Nat.land J (nat_lit 3)) (nat_lit 0))

@[expose] noncomputable def runChunk (blk LT HT PBT WT : Nat → Nat) (NL TL NB BB NH ND NO C S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih J S => strictN (WT (Nat.land (Nat.shiftRight J (nat_lit 2)) (nat_lit 255))) (fun w =>
      strictN (factStep blk LT HT PBT NL TL NB BB NH ND NO J S (fct blk (sI S)) w) (fun S' =>
        ih (Nat.shiftRight J (jLen J w)) S')))
    (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S

@[expose] noncomputable def runFacts (blk LT HT PBT WT : Nat → Nat) (NL TL NB BB NH ND NO : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (runChunk blk LT HT PBT WT NL TL NB BB NH ND NO C S) ih) Cs

@[expose] noncomputable def covEntry (blk PBT OMT : Nat → Nat) (NB ALIVE nf D w e : Nat) : Bool :=
  andB (Nat.blt (Nat.shiftRight e (nat_lit 1)) nf)
    (letB (fct blk (Nat.shiftRight e (nat_lit 1))) (fun R =>
      Bool.rec (motive := fun _ => Bool)
        (andB (Nat.beq (dD R) D) (andB (Nat.beq (dJ R) (Nat.succ w)) (bitAt ALIVE (dDp R))))
        (andB (Nat.beq (dDp R) D) (andB (Nat.blt (nat_lit 0) (dJ R)) (andB (bitAt ALIVE (dD R))
          (allMemb NB (OMT (Nat.sub (dJ R) (nat_lit 1))) (imgMasks (dP R) (PBT w))))))
        (Nat.beq (Nat.land e (nat_lit 1)) (nat_lit 1))))

@[expose] noncomputable def covChunk (blk PBT OMT : Nat → Nat) (NB NO hi ALIVE nf C X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ X => X)
    (fun _ ih J X =>
      Bool.rec (motive := fun _ => Nat)
        (strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ X) (Nat.blt (nat_lit 0) X)) (ih J))
        (strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ X)
            (andB (Nat.blt (nat_lit 0) X) (allBelow NO hi (fun w =>
              covEntry blk PBT OMT NB ALIVE nf (Nat.sub X (nat_lit 1)) w
                (Nat.land (Nat.shiftRight J (Nat.mul (nat_lit 32) w)) m32))))) (fun X' =>
          strictN (Nat.shiftRight J (Nat.mul (nat_lit 32) NO)) (fun J' => ih J' X')))
        (bitAt ALIVE (Nat.sub X (nat_lit 1))))
    (Nat.land C (nat_lit 65535)) (Nat.shiftRight C (nat_lit 16)) X

@[expose] noncomputable def runCover (blk PBT OMT : Nat → Nat) (NB NO hi ALIVE nf : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun X => X)
    (fun C _ ih X => strictN (covChunk blk PBT OMT NB NO hi ALIVE nf C X) ih) Cs

@[expose] noncomputable def eRec (ET : Nat → Nat) (i : Nat) : Nat :=
  strictN (Nat.shiftRight i (nat_lit 8)) (fun k =>
    Nat.land (Nat.shiftRight (ET k) (Nat.shiftLeft (Nat.land i (nat_lit 255)) (nat_lit 8)))
      (nat_lit 115792089237316195423570985008687907853269984665640564039457584007913129639935))

@[expose] noncomputable def eP (Q : Nat) : Nat := Nat.land (Nat.shiftRight Q (nat_lit 64)) m20
@[expose] noncomputable def eK (Q : Nat) : Nat := Nat.land (Nat.shiftRight Q (nat_lit 84)) (nat_lit 15)
@[expose] noncomputable def eRank (Q : Nat) : Nat := Nat.land (Nat.shiftRight Q (nat_lit 88)) m20
@[expose] noncomputable def eRoot (Q : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight Q (nat_lit 108)) (nat_lit 1)) (nat_lit 1)
@[expose] noncomputable def eC (Q k : Nat) : Nat :=
  Nat.land (Nat.shiftRight Q (Nat.add (nat_lit 112) (Nat.mul (nat_lit 20) k))) m20
@[expose] noncomputable def gk (G k : Nat) : Nat := Nat.land (Nat.shiftRight G (Nat.mul (nat_lit 64) k)) m64

@[expose] noncomputable def eCnt (S : Nat) : Nat := Nat.land S (nat_lit 16777215)
@[expose] noncomputable def ePrev (S : Nat) : Nat := Nat.shiftRight S (nat_lit 24)

@[expose] noncomputable def eStep (ET : Nat → Nat) (G ng n off S : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0)
    (strictN (eRec ET (Nat.add off (Nat.sub (eCnt S) (nat_lit 1)))) (fun Q =>
      Bool.rec (motive := fun _ => Nat) (nat_lit 0)
        (Nat.lor (Nat.succ (eCnt S)) (Nat.shiftLeft (Nat.land Q m64) (nat_lit 24)))
        (andB (orB (Nat.beq (eCnt S) (nat_lit 1)) (Nat.blt (ePrev S) (Nat.land Q m64)))
        (andB (Bool.rec (motive := fun _ => Bool)
            (andB (Nat.blt (eP Q) n) (andB (Nat.blt (eK Q) ng)
              (letB (eRec ET (Nat.add off (eP Q))) (fun P =>
                andB (Nat.blt (eRank P) (eRank Q))
                  (Nat.beq (Nat.land Q m64) (pmul (Nat.land P m64) (gk G (eK Q))))))))
            (Nat.beq (Nat.land Q m64) idP)
            (eRoot Q))
          (Nat.rec (motive := fun _ => Bool) true (fun k acc => andB acc
            (andB (Nat.blt (eC Q k) n)
              (Nat.beq (pmul (Nat.land Q m64) (gk G k)) (Nat.land (eRec ET (Nat.add off (eC Q k))) m64)))) ng)))))
    (andB (Nat.blt (nat_lit 0) S) (Nat.ble (eCnt S) n))

@[expose] noncomputable def enumRun (ET : Nat → Nat) (G ng n off m : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun _ ih S => strictN (eStep ET G ng n off S) ih) m

@[expose] noncomputable def packGens (f : Nat → Nat) (ng : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.lor acc (Nat.shiftLeft (Nat.land (f k) m64) (Nat.mul (nat_lit 64) k))) ng

@[expose] noncomputable def nGens (LT : Nat → Nat) (NL TL : Nat) : Nat :=
  packGens (fun k => LT (Bool.rec (motive := fun _ => Nat) (Nat.succ k) k (Nat.blt k TL))) (Nat.sub NL (nat_lit 1))

@[expose] noncomputable def stN (T : Nat) : Nat := Nat.land T (nat_lit 16777215)
@[expose] noncomputable def stOff (T : Nat) : Nat := Nat.land (Nat.shiftRight T (nat_lit 24)) (nat_lit 16777215)
@[expose] noncomputable def stGL (T : Nat) : Nat := Nat.shiftRight T (nat_lit 48)
@[expose] noncomputable def glN (GL : Nat) : Nat := Nat.land GL (nat_lit 255)
@[expose] noncomputable def glH (GL k : Nat) : Nat :=
  Nat.land (Nat.shiftRight GL (Nat.add (nat_lit 8) (Nat.mul (nat_lit 24) k))) (nat_lit 16777215)

@[expose] noncomputable def gensStab (blk : Nat → Nat) (nf D GL : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k acc => andB acc
    (andB (Nat.blt (glH GL k) nf) (dStab (fct blk (glH GL k)) D))) (glN GL)

@[expose] noncomputable def failV : Nat := nat_lit 18446744073709551616

@[expose] noncomputable def stabVal (blk SE STT : Nat → Nat) (nf nN D : Nat) : Nat :=
  strictN (STT D) (fun T =>
    Bool.rec (motive := fun _ => Nat) failV (Nat.div nN (stN T))
      (andB (Nat.blt (nat_lit 0) (stN T)) (andB (Nat.beq (Nat.mod nN (stN T)) (nat_lit 0))
      (andB (Nat.ble (glN (stGL T)) (nat_lit 7)) (andB (gensStab blk nf D (stGL T))
        (Nat.beq (eCnt (enumRun SE (packGens (fun k => dP (fct blk (glH (stGL T) k))) (glN (stGL T)))
            (glN (stGL T)) (stN T) (stOff T) (stN T) (nat_lit 1)))
          (Nat.succ (stN T))))))))

@[expose] noncomputable def indexSum (blk SE STT : Nat → Nat) (nf nN ND hi ALIVE : Nat) : Nat :=
  sumBelow ND hi (fun D => Bool.rec (motive := fun _ => Nat) (nat_lit 0)
    (Bool.rec (motive := fun _ => Nat) (stabVal blk SE STT nf nN D) (nat_lit 1) (Nat.beq D (nat_lit 0)))
    (bitAt ALIVE D))

end CFSG.KC.DceS

end
