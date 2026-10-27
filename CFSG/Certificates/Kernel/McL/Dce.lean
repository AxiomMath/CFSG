module

public import CFSG.Certificates.Kernel.McL.Mat25
public import CFSG.Certificates.Kernel.Th.Words
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.McL.Dce

open CFSG.KC.Th CFSG.KC.Loop CFSG.KC.McL.Mat

@[expose] def M20 : Nat := nat_lit 1048575

@[expose] noncomputable def rec (FB : Nat → Nat) (sh wd h : Nat) : Nat :=
  strictN (Nat.shiftRight h sh) (fun k =>
    Nat.shiftRight (FB k) (Nat.mul (Nat.sub h (Nat.shiftLeft k sh)) wd))

@[expose] noncomputable def mat (HB : Nat → Nat) (h : Nat) : Nat :=
  Nat.land (rec HB (nat_lit 6) (nat_lit 625) h) m625

@[expose] noncomputable def e40 (B : Nat → Nat) (j : Nat) : Nat :=
  Nat.land (rec B (nat_lit 8) (nat_lit 40) j) (nat_lit 1099511627775)

@[expose] noncomputable def lo20 (x : Nat) : Nat := Nat.land x M20
@[expose] noncomputable def hi20 (x : Nat) : Nat := Nat.shiftRight x (nat_lit 20)

@[expose] noncomputable def pt (OB : Nat → Nat) (w : Nat) : Nat :=
  Nat.land (rec OB (nat_lit 8) (nat_lit 25) w) Mat.rowMask

@[expose] noncomputable def let25 (LT c : Nat) : Nat :=
  Nat.land (Nat.shiftRight LT (Nat.mul c (nat_lit 625))) m625

@[expose] noncomputable def byte (x i : Nat) : Nat := Nat.land (Nat.shiftRight x (Nat.mul (nat_lit 8) i)) (nat_lit 255)

@[expose] noncomputable def notB (b : Bool) : Bool := Bool.rec true false b

@[expose] noncomputable def bits (J o x : Nat) : Nat :=
  Nat.land (Nat.shiftRight J o) (Nat.sub (Nat.shiftLeft (nat_lit 1) x) (nat_lit 1))

@[expose] noncomputable def rD (R : Nat) : Nat := Nat.land R (nat_lit 255)
@[expose] noncomputable def rJ (R : Nat) : Nat := Nat.land (Nat.shiftRight R (nat_lit 8)) (nat_lit 65535)
@[expose] noncomputable def rDp (R : Nat) : Nat := Nat.land (Nat.shiftRight R (nat_lit 24)) (nat_lit 255)
@[expose] noncomputable def rPi (R : Nat) : Nat := Nat.land (Nat.shiftRight R (nat_lit 32)) m625
@[expose] noncomputable def rFI (R : Nat) : Nat := Nat.land (Nat.shiftRight R (nat_lit 657)) m625
@[expose] noncomputable def rN (R : Nat) : Nat := Nat.land (Nat.shiftRight R (nat_lit 1282)) m625
@[expose] noncomputable def rNI (R : Nat) : Nat := Nat.land (Nat.shiftRight R (nat_lit 1907)) m625

@[expose] def RW : Nat := nat_lit 2532

@[expose] noncomputable def mkSt (D p : Nat) : Nat := Nat.lor D (Nat.shiftLeft p (nat_lit 8))
@[expose] noncomputable def sD (S : Nat) : Nat := Nat.land S (nat_lit 255)
@[expose] noncomputable def sPi (S : Nat) : Nat := Nat.shiftRight S (nat_lit 8)
@[expose] def bad : Nat := nat_lit 255

@[expose] noncomputable def isN (TL NL c : Nat) : Bool := andB (Nat.blt c NL) (notB (Nat.beq c TL))

@[expose] noncomputable def stepE (R dir S : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) bad
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) bad (mkSt (rDp R) (mul25 (rPi R) (sPi S))) (Nat.beq (sD S) (rD R)))
      (Bool.rec (motive := fun _ => Nat) bad (mkSt (rD R) (mul25 (rFI R) (sPi S))) (Nat.beq (sD S) (rDp R)))
      (Nat.beq dir (nat_lit 1)))
    (Nat.beq (rJ R) (nat_lit 0))

@[expose] noncomputable def stepT (HB GB TB : Nat → Nat) (nT R dir e S : Nat) : Nat :=
  (fun g t => (fun G Gi TS TP =>
    Bool.rec (motive := fun _ => Nat) bad
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) bad
          (mkSt (rDp R) (mul25 (mul25 (rPi R) Gi) TP))
          (andB (Nat.beq (sD S) (rD R)) (Nat.beq TS (mul25 G (sPi S)))))
        (Bool.rec (motive := fun _ => Nat) bad
          (mkSt (rD R) (mul25 Gi TS))
          (andB (Nat.beq (sD S) (rDp R)) (Nat.beq TP (mul25 (mul25 G (rFI R)) (sPi S)))))
        (Nat.beq dir (nat_lit 1)))
      (andB (Nat.blt (nat_lit 0) (rJ R)) (Nat.blt e nT)))
    (mat HB (lo20 g)) (mat HB (hi20 g)) (mat HB (lo20 t)) (mat HB (hi20 t)))
  (e40 GB (Nat.sub (rJ R) (nat_lit 1))) (e40 TB e)

@[expose] noncomputable def stepL (HB GB TB : Nat → Nat) (TL nT c R dir e S : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) bad (stepT HB GB TB nT R dir e S) (Nat.beq c TL))
    (stepE R dir S) (Nat.beq c (nat_lit 255))

@[expose] noncomputable def posBits (TL c : Nat) (own : Bool) : Nat :=
  Nat.add (Bool.rec (motive := fun _ => Nat) (nat_lit 21) (nat_lit 0) own)
    (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 17) (Nat.beq c TL))

@[expose] noncomputable def walkGo (FB HB GB TB : Nat → Nat) (LT TL NL nT : Nat)
    (i Ri ft fd Wd n : Nat) (k : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat)
    (fun _ S A => Nat.lor S (Nat.shiftLeft A (nat_lit 640)))
    (fun k ih J S A => (fun q => (fun c =>
      Bool.rec (motive := fun _ => Nat)
        (ih J (mkSt (sD S) (mul25 (sPi S) (let25 LT c))) A)
        ((fun own => (fun h => (fun R dir =>
            Bool.rec (motive := fun _ => Nat) bad
              (strictN (stepL HB GB TB TL nT c R dir
                  (Bool.rec (motive := fun _ => Nat) (bits J (nat_lit 21) (nat_lit 17)) (bits J (nat_lit 0) (nat_lit 17)) own) S)
                (fun S2 => ih (Nat.shiftRight J (posBits TL c own)) S2
                  (mul25 A (Bool.rec (motive := fun _ => Nat) (rN R) (rNI R) (Nat.beq dir (nat_lit 1))))))
              (orB own (Nat.blt h i)))
            (Bool.rec (motive := fun _ => Nat) (rec FB (nat_lit 6) RW h) Ri own)
            (Bool.rec (motive := fun _ => Nat) (Nat.land J (nat_lit 1)) fd own))
          (bits J (nat_lit 1) (nat_lit 20)))
         (Nat.beq q ft))
        (notB (isN TL NL c)))
      (byte Wd q)) (Nat.sub n (Nat.succ k))) k

@[expose] noncomputable def sI (S : Nat) : Nat := Nat.land S (nat_lit 4294967295)
@[expose] noncomputable def sX (S : Nat) : Nat := Nat.shiftRight S (nat_lit 32)
@[expose] noncomputable def mkS (i nx : Nat) : Nat := Nat.lor i (Nat.shiftLeft nx (nat_lit 32))

@[expose] noncomputable def recOK (ND NO R : Nat) : Bool :=
  andB (Nat.blt (rD R) ND) (andB (Nat.blt (rDp R) ND) (andB (Nat.ble (rJ R) NO)
    (andB (Nat.beq (mul25 (rPi R) (rFI R)) ident) (Nat.beq (mul25 (rN R) (rNI R)) ident))))

@[expose] noncomputable def treeOK (nx R : Nat) : Bool :=
  andB (Nat.blt (nat_lit 0) (rJ R)) (andB (Nat.beq (rDp R) nx) (andB (Nat.blt (rD R) nx)
    (andB (Nat.beq (rPi R) ident) (Nat.beq (rN R) ident))))

@[expose] noncomputable def axiomOK (HB : Nat → Nat) (nH Jf R : Nat) : Bool :=
  (fun x b => andB (Nat.beq (rD R) (nat_lit 0)) (andB (Nat.beq (rJ R) (nat_lit 0)) (andB (Nat.beq (rDp R) (nat_lit 0))
    (andB (Nat.blt x nH) (andB (Nat.blt b nH) (andB (Nat.beq (rPi R) (mul25 (mat HB x) (mat HB b)))
      (Nat.beq (rN R) (rFI R))))))))
  (bits Jf (nat_lit 2) (nat_lit 20)) (bits Jf (nat_lit 22) (nat_lit 20))

@[expose] noncomputable def walkOK (FB HB GB TB WD : Nat → Nat) (LT TL NL ND nH nT nW : Nat)
    (i Jf R : Nat) : Bool :=
  (fun w D0 x b ft fd => (fun e => (fun n Wd => (fun S0 =>
      andB (Nat.blt w nW) (andB (Nat.blt D0 ND) (andB (Nat.blt x nH) (andB (Nat.blt b nH)
        (andB (Nat.blt ft n) (andB (notB (isN TL NL (byte Wd ft)))
          (Nat.beq (walkGo FB HB GB TB LT TL NL nT i R ft fd Wd n n (Nat.shiftRight Jf (nat_lit 77)) S0 ident)
            (Nat.lor S0 (Nat.shiftLeft ident (nat_lit 640))))))))))
      (mkSt D0 (mul25 (mat HB x) (mat HB b))))
    (bits e (nat_lit 2) (nat_lit 10)) (Nat.shiftRight e (nat_lit 12))) (WD w))
  (bits Jf (nat_lit 2) (nat_lit 16)) (bits Jf (nat_lit 18) (nat_lit 8)) (bits Jf (nat_lit 26) (nat_lit 20))
  (bits Jf (nat_lit 46) (nat_lit 20)) (bits Jf (nat_lit 66) (nat_lit 10)) (bits Jf (nat_lit 76) (nat_lit 1))

@[expose] noncomputable def factStep (FB HB GB TB WD : Nat → Nat) (LT TL NL ND NO nH nT nW : Nat)
    (Jf S : Nat) : Nat :=
  (fun i nx R k => Bool.rec (motive := fun _ => Nat) (nat_lit 0)
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat)
          (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (mkS (Nat.succ i) nx)
            (andB (Nat.beq k (nat_lit 2)) (walkOK FB HB GB TB WD LT TL NL ND nH nT nW i Jf R)))
          (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (mkS (Nat.succ i) nx) (axiomOK HB nH Jf R))
          (Nat.beq k (nat_lit 1)))
        (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (mkS (Nat.succ i) (Nat.succ nx)) (treeOK nx R))
        (Nat.beq k (nat_lit 0)))
      (andB (Nat.blt (nat_lit 0) S) (recOK ND NO R)))
    (sI S) (sX S) (rec FB (nat_lit 6) RW (sI S)) (Nat.land Jf (nat_lit 3))

@[expose] noncomputable def runChunk (FB HB GB TB WD : Nat → Nat) (LT TL NL ND NO nH nT nW : Nat)
    (C S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih J S => (fun L =>
      strictN (factStep FB HB GB TB WD LT TL NL ND NO nH nT nW (bits J (nat_lit 12) L) S)
        (ih (Nat.shiftRight J (Nat.add (nat_lit 12) L))))
      (Nat.land J (nat_lit 4095)))
    (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S

@[expose] noncomputable def runFacts (FB HB GB TB WD : Nat → Nat) (LT TL NL ND NO nH nT nW : Nat)
    (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (runChunk FB HB GB TB WD LT TL NL ND NO nH nT nW C S) ih) Cs

@[expose] noncomputable def hdrOK (HB : Nat → Nat) (LT TL NL h d : Nat) : Bool :=
  (fun k a b H => Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false
          (andB (Nat.blt a h) (Nat.beq (mul25 H (mat HB a)) ident)) (Nat.beq k (nat_lit 3)))
        (andB (Nat.blt a h) (andB (Nat.blt b h) (Nat.beq H (mul25 (mat HB a) (mat HB b))))) (Nat.beq k (nat_lit 2)))
      (andB (isN TL NL a) (Nat.beq H (let25 LT a))) (Nat.beq k (nat_lit 1)))
    (Nat.beq H ident) (Nat.beq k (nat_lit 0)))
  (Nat.land d (nat_lit 7)) (bits d (nat_lit 3) (nat_lit 20)) (bits d (nat_lit 23) (nat_lit 20)) (mat HB h)

@[expose] noncomputable def runHdr (HB : Nat → Nat) (LT TL NL : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
            (andB (Nat.blt (nat_lit 0) S) (hdrOK HB LT TL NL (Nat.sub S (nat_lit 1)) (bits J (nat_lit 0) (nat_lit 43)))))
          (ih2 (Nat.shiftRight J (nat_lit 43))))
        (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S) ih) Cs

@[expose] noncomputable def gomOK (HB GB OB : Nat → Nat) (I0 nH j : Nat) : Bool :=
  (fun g => andB (Nat.blt (lo20 g) nH) (andB (Nat.blt (hi20 g) nH)
    (andB (Nat.beq (pt OB j) (Mat.vecmul (pt OB I0) (mat HB (lo20 g))))
      (Nat.beq (mul25 (mat HB (lo20 g)) (mat HB (hi20 g))) ident))))
  (e40 GB j)

@[expose] noncomputable def runGom (HB GB OB : Nat → Nat) (I0 nH : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat) (fun S => S)
        (fun _ ih2 S => strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
            (andB (Nat.blt (nat_lit 0) S) (gomOK HB GB OB I0 nH (Nat.sub S (nat_lit 1)))))
          ih2)
        (Nat.land C (nat_lit 65535)) S) ih) Cs

@[expose] noncomputable def runSorted (get : Nat → Nat) (qb m : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => (fun q => strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
            (Nat.lor (Nat.succ (Nat.land S M20)) (Nat.shiftLeft (get q) (nat_lit 20)))
            (andB (Nat.blt (nat_lit 0) S) (andB (Nat.blt q m) (Nat.blt (Nat.shiftRight S (nat_lit 20)) (get q)))))
          (ih2 (Nat.shiftRight J qb))) (bits J (nat_lit 0) qb))
        (Nat.land C (nat_lit 65535)) (Nat.shiftRight C (nat_lit 16)) S) ih) Cs

@[expose] noncomputable def tSig (HB TB : Nat → Nat) (e : Nat) : Nat := mat HB (lo20 (e40 TB e))

@[expose] noncomputable def sortedCount (S : Nat) : Nat := Nat.sub (Nat.land S M20) (nat_lit 1)

@[expose] noncomputable def segProd (LT TL NL Wd o m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ident
    (fun k acc => (fun c => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (mul25 acc (let25 LT c)) (isN TL NL c))
      (byte Wd (Nat.add o k))) m

@[expose] noncomputable def relVisOK (RR : Nat → Nat) (LT TL NL NR S P r s ns : Nat) : Bool :=
  (fun e => (fun n => (fun Wd => andB (Nat.blt r NR) (andB (Nat.blt s n) (andB (Nat.ble (Nat.add ns (nat_lit 2)) n)
      (andB (Nat.beq (byte Wd (nat_lit 0)) TL) (andB (Nat.beq (byte Wd (Nat.succ ns)) TL)
        (andB (Nat.beq S (segProd LT TL NL Wd (nat_lit 1) ns))
          (Nat.beq (mul25 P (segProd LT TL NL Wd (Nat.add ns (nat_lit 2)) (Nat.sub n (Nat.add ns (nat_lit 2))))) ident)))))))
    (rot (Nat.shiftRight e (nat_lit 12)) n s)) (bits e (nat_lit 2) (nat_lit 10))) (RR r)

@[expose] noncomputable def tOK (HB TB OB RR : Nat → Nat) (LT TL NL NR nH nT I0 e d : Nat) : Bool :=
  (fun t k p => (fun S P => andB (Nat.blt (lo20 t) nH) (andB (Nat.blt (hi20 t) nH)
      (andB (Nat.blt (bits d (nat_lit 42) (nat_lit 17)) nT)
        (andB (Nat.beq P (mat HB (lo20 (e40 TB (bits d (nat_lit 42) (nat_lit 17))))))
          (andB (Nat.beq (Mat.vecmul (pt OB I0) S) (pt OB I0))
            (Bool.rec (motive := fun _ => Bool)
              (Bool.rec (motive := fun _ => Bool) false
                (relVisOK RR LT TL NL NR S P (bits p (nat_lit 0) (nat_lit 8)) (bits p (nat_lit 8) (nat_lit 10))
                  (bits p (nat_lit 18) (nat_lit 10)))
                (Nat.beq k (nat_lit 1)))
              ((fun a b => andB (Nat.blt a e) (andB (Nat.blt b e)
                  (andB (Nat.beq S (mul25 (mat HB (lo20 (e40 TB a))) (mat HB (lo20 (e40 TB b)))))
                    (Nat.beq P (mul25 (mat HB (hi20 (e40 TB a))) (mat HB (hi20 (e40 TB b))))))))
                (bits p (nat_lit 0) (nat_lit 17)) (bits p (nat_lit 17) (nat_lit 17)))
              (Nat.beq k (nat_lit 0))))))))
    (mat HB (lo20 t)) (mat HB (hi20 t)))
  (e40 TB e) (Nat.land d (nat_lit 3)) (bits d (nat_lit 2) (nat_lit 40))

@[expose] noncomputable def runT (HB TB OB RR : Nat → Nat) (LT TL NL NR nH nT I0 : Nat)
    (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
            (andB (Nat.blt (nat_lit 0) S)
              (tOK HB TB OB RR LT TL NL NR nH nT I0 (Nat.sub S (nat_lit 1)) (bits J (nat_lit 0) (nat_lit 59)))))
          (ih2 (Nat.shiftRight J (nat_lit 59))))
        (Nat.land C (nat_lit 65535)) (Nat.shiftRight C (nat_lit 16)) S) ih) Cs

@[expose] noncomputable def aliveD (AL D : Nat) : Bool := Nat.blt (nat_lit 0) (Nat.land AL (Nat.shiftLeft (nat_lit 1) D))

@[expose] noncomputable def slotOK (FB OB : Nat → Nat) (NF AL D w x : Nat) : Bool :=
  (fun g => (fun R => andB (Nat.blt g NF)
      (Bool.rec (motive := fun _ => Bool)
        (andB (Nat.beq (rD R) D) (andB (Nat.beq (rJ R) (Nat.succ w)) (aliveD AL (rDp R))))
        (andB (Nat.beq (rDp R) D) (andB (Nat.blt (nat_lit 0) (rJ R)) (andB (aliveD AL (rD R))
          (Nat.beq (Mat.vecmul (pt OB w) (rPi R)) (pt OB (Nat.sub (rJ R) (nat_lit 1)))))))
        (Nat.beq (Nat.land x (nat_lit 1)) (nat_lit 1))))
    (rec FB (nat_lit 6) RW g)) (Nat.shiftRight x (nat_lit 1))

@[expose] noncomputable def runCover (FB OB : Nat → Nat) (NF NO AL : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => (fun D w => (fun nxt =>
            Bool.rec (motive := fun _ => Nat) (nat_lit 0)
              (Bool.rec (motive := fun _ => Nat)
                (strictN nxt (ih2 J))
                (strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0) nxt
                    (slotOK FB OB NF AL D w (bits J (nat_lit 0) (nat_lit 21))))
                  (ih2 (Nat.shiftRight J (nat_lit 21))))
                (aliveD AL D))
              (Nat.blt (nat_lit 0) S))
            (Bool.rec (motive := fun _ => Nat) (Nat.add S (nat_lit 1))
              (Nat.add (nat_lit 1) (Nat.shiftLeft (Nat.succ D) (nat_lit 20)))
              (orB (notB (aliveD AL D)) (Nat.beq (Nat.succ w) NO))))
          (Nat.shiftRight (Nat.sub S (nat_lit 1)) (nat_lit 20)) (Nat.land (Nat.sub S (nat_lit 1)) M20))
        (Nat.land C (nat_lit 65535)) (Nat.shiftRight C (nat_lit 16)) S) ih) Cs

@[expose] noncomputable def stabGen (FB : Nat → Nat) (NF D SG s : Nat) : Nat :=
  (fun g => (fun R => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (rPi R)
      (andB (Nat.blt s (Nat.land SG (nat_lit 31))) (andB (Nat.blt g NF) (andB (Nat.beq (rD R) D)
        (andB (Nat.beq (rJ R) (nat_lit 0)) (Nat.beq (rDp R) D))))))
    (rec FB (nat_lit 6) RW g))
  (bits SG (Nat.add (nat_lit 5) (Nat.mul (nat_lit 20) s)) (nat_lit 20))

@[expose] noncomputable def runStab (FB EB : Nat → Nat) (NF D SG : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
            ((fun k p s => andB (Nat.blt (nat_lit 0) S) (andB (Nat.blt p k)
                (Nat.beq (mat EB k) (mul25 (mat EB p) (stabGen FB NF D SG s)))))
              (Nat.sub S (nat_lit 1)) (bits J (nat_lit 0) (nat_lit 17)) (bits J (nat_lit 17) (nat_lit 5))))
          (ih2 (Nat.shiftRight J (nat_lit 22))))
        (Nat.land C (nat_lit 65535)) (Nat.shiftRight C (nat_lit 16)) S) ih) Cs

@[expose] noncomputable def stabStart (EB : Nat → Nat) : Bool := Nat.beq (mat EB (nat_lit 0)) ident

@[expose] noncomputable def sumOK (AL MD ND NORD SUM : Nat) : Bool :=
  andB (aliveD AL (nat_lit 0)) (andB (Nat.blt AL (Nat.shiftLeft (nat_lit 1) ND))
    ((fun r => andB (Nat.blt (nat_lit 0) r) (Nat.beq (Nat.sub r (nat_lit 1)) SUM))
      (Nat.rec (motive := fun _ => Nat) (nat_lit 2)
        (fun D acc => (fun m => Bool.rec (motive := fun _ => Nat) acc
            (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.add acc (Nat.div NORD m))
              (andB (Nat.blt (nat_lit 0) acc) (andB (Nat.blt (nat_lit 0) m) (Nat.beq (Nat.mod NORD m) (nat_lit 0)))))
            (andB (aliveD AL D) (notB (Nat.beq D (nat_lit 0)))))
          (bits MD (Nat.mul (nat_lit 20) D) (nat_lit 20)))
        ND)))

@[expose] noncomputable def lettersOK (LT LI TL NL : Nat) : Bool :=
  andB (Nat.blt NL (nat_lit 255)) (andB (Nat.blt TL NL)
    (Nat.rec (motive := fun _ => Bool) true (fun c ih => andB ih
      (andB (Nat.beq (byte LI c) c)
        (Bool.rec (motive := fun _ => Bool) true
          (Nat.beq (mul25 (let25 LT c) (let25 LT c)) ident) (isN TL NL c)))) NL))

@[expose] noncomputable def relsOK (RR : Nat → Nat) (NL NR : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun r ih => andB ih
    ((fun e => Nat.rec (motive := fun _ => Bool) true
        (fun i ih2 => andB ih2 (Nat.blt (byte (Nat.shiftRight e (nat_lit 12)) i) NL)) (bits e (nat_lit 2) (nat_lit 10)))
      (RR r))) NR

@[expose] noncomputable def wordOK (WD RR : Nat → Nat) (LI NL NR WH w : Nat) : Bool :=
  (fun e h => (fun n Wd => andB (Nat.blt h NR)
      (andB (Nat.rec (motive := fun _ => Bool) true (fun i ih => andB ih
          (orB (Nat.blt (byte Wd i) NL) (Nat.beq (byte Wd i) (nat_lit 255)))) n)
        (chkWord LI Wd n (Nat.shiftRight (RR h) (nat_lit 12)) (bits (RR h) (nat_lit 2) (nat_lit 10)))))
    (bits e (nat_lit 2) (nat_lit 10)) (Nat.shiftRight e (nat_lit 12)))
  (WD w) (byte WH w)

@[expose] noncomputable def wordsOK (WD RR : Nat → Nat) (LI NL NR WH nW : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun w ih => andB ih (wordOK WD RR LI NL NR WH w)) nW

@[expose] noncomputable def tsqOK (RR : Nat → Nat) (TL NR h : Nat) : Bool :=
  andB (Nat.blt h NR) (Nat.beq (RR h) (Nat.add (nat_lit 8) (Nat.shiftLeft (Nat.add TL (Nat.mul (nat_lit 256) TL)) (nat_lit 12))))

@[expose] noncomputable def nRelsHold (LT : Nat) (REL : Nat → Nat) (TL NL NR : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun r ih => andB ih
    ((fun e => (fun n Wd => Nat.beq
        (Nat.rec (motive := fun _ => Nat) ident
          (fun i acc => (fun g => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (mul25 acc (let25 LT g)) (isN TL NL g))
            (Nat.shiftRight (byte Wd i) (nat_lit 1))) n)
        ident)
      (bits e (nat_lit 2) (nat_lit 10)) (Nat.shiftRight e (nat_lit 12)))
      (REL r))) NR

@[expose] noncomputable def traceOK (FB HB GB TB : Nat → Nat) (LT TL NL nT NF Wd n J : Nat) : Bool :=
  (fun res => (fun S A => andB (Nat.beq (sD S) (nat_lit 0)) (Nat.beq (mul25 A (sPi S)) ident))
      (Nat.land res (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 640)) (nat_lit 1))) (Nat.shiftRight res (nat_lit 640)))
    (Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat)
      (fun _ S A => Nat.lor S (Nat.shiftLeft A (nat_lit 640)))
      (fun k ih J S A => (fun c =>
          Bool.rec (motive := fun _ => Nat)
            (ih J (mkSt (sD S) (mul25 (sPi S) (let25 LT c))) A)
            ((fun h => (fun R dir => Bool.rec (motive := fun _ => Nat) bad
                (strictN (stepL HB GB TB TL nT c R dir (bits J (nat_lit 21) (nat_lit 17)) S)
                  (fun S2 => ih (Nat.shiftRight J (nat_lit 38)) S2
                    (mul25 A (Bool.rec (motive := fun _ => Nat) (rN R) (rNI R) (Nat.beq dir (nat_lit 1))))))
                (andB (Nat.blt h NF) (Nat.beq c TL)))
              (rec FB (nat_lit 6) RW h) (Nat.land J (nat_lit 1)))
              (bits J (nat_lit 1) (nat_lit 20)))
            (notB (isN TL NL c)))
        (byte Wd (Nat.sub n (Nat.succ k)))) n J (mkSt (nat_lit 0) ident) ident)

@[expose] noncomputable def membWordOK (e c : Nat) : Bool :=
  (fun n Wd => andB (Nat.blt (nat_lit 0) n) (andB (Nat.beq (byte Wd (nat_lit 0)) c)
      (Nat.rec (motive := fun _ => Bool) true
        (fun i ih => andB ih (notB (Nat.beq (byte Wd (Nat.succ i)) c))) (Nat.sub n (nat_lit 1)))))
    (bits e (nat_lit 2) (nat_lit 10)) (Nat.shiftRight e (nat_lit 12))

end CFSG.KC.McL.Dce

end
