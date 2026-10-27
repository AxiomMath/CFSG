module

public import CFSG.Certificates.Kernel.Th.Words
public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Certificates.Kernel.Th.S.Hsw

public section

namespace CFSG.KC.Th.DceS

open CFSG.KC.Th CFSG.KC.Loop

@[expose] def M576 : Nat := nat_lit 247330401473104534060502521019647190035131349101211839914063056092897225106531867170316401061243044989597671426016139339351365034306751209967546155101893167916606772148699135
@[expose] def M20 : Nat := nat_lit 1048575

@[expose] noncomputable def rec (FB : Nat → Nat) (sh wd h : Nat) : Nat :=
  strictN (Nat.shiftRight h sh) (fun k =>
    Nat.shiftRight (FB k) (Nat.mul (Nat.sub h (Nat.shiftLeft k sh)) wd))

@[expose] noncomputable def mat (HB : Nat → Nat) (h : Nat) : Nat :=
  Nat.land (rec HB (nat_lit 6) (nat_lit 576) h) M576

@[expose] noncomputable def e40 (B : Nat → Nat) (j : Nat) : Nat :=
  Nat.land (rec B (nat_lit 8) (nat_lit 40) j) (nat_lit 1099511627775)

@[expose] noncomputable def lo20 (x : Nat) : Nat := Nat.land x M20
@[expose] noncomputable def hi20 (x : Nat) : Nat := Nat.shiftRight x (nat_lit 20)

@[expose] noncomputable def pt (OB : Nat → Nat) (osh owd om w : Nat) : Nat :=
  Nat.land (rec OB osh owd w) om

@[expose] noncomputable def let24 (LT c : Nat) : Nat :=
  Nat.land (Nat.shiftRight LT (Nat.mul c (nat_lit 576))) M576

@[expose] noncomputable def byte (x i : Nat) : Nat := Nat.land (Nat.shiftRight x (Nat.mul (nat_lit 8) i)) (nat_lit 255)

@[expose] noncomputable def notB (b : Bool) : Bool := Bool.rec true false b

@[expose] noncomputable def bits (J o x : Nat) : Nat :=
  Nat.land (Nat.shiftRight J o) (Nat.sub (Nat.shiftLeft (nat_lit 1) x) (nat_lit 1))

@[expose] noncomputable def rD (R : Nat) : Nat := Nat.land R (nat_lit 255)
@[expose] noncomputable def rJ (R : Nat) : Nat := Nat.land (Nat.shiftRight R (nat_lit 8)) (nat_lit 65535)
@[expose] noncomputable def rDp (R : Nat) : Nat := Nat.land (Nat.shiftRight R (nat_lit 24)) (nat_lit 255)
@[expose] noncomputable def rPi (R : Nat) : Nat := Nat.land (Nat.shiftRight R (nat_lit 32)) M576
@[expose] noncomputable def rFI (R : Nat) : Nat := Nat.land (Nat.shiftRight R (nat_lit 608)) M576
@[expose] noncomputable def rN (R : Nat) : Nat := Nat.land (Nat.shiftRight R (nat_lit 1184)) M576
@[expose] noncomputable def rNI (R : Nat) : Nat := Nat.land (Nat.shiftRight R (nat_lit 1760)) M576

@[expose] noncomputable def mkSt (D p : Nat) : Nat := Nat.lor D (Nat.shiftLeft p (nat_lit 8))
@[expose] noncomputable def sD (S : Nat) : Nat := Nat.land S (nat_lit 255)
@[expose] noncomputable def sPi (S : Nat) : Nat := Nat.shiftRight S (nat_lit 8)
@[expose] def bad : Nat := nat_lit 255

@[expose] noncomputable def isN (TL VL NL c : Nat) : Bool :=
  andB (Nat.blt c NL) (andB (notB (Nat.beq c TL)) (notB (Nat.beq c VL)))

@[expose] noncomputable def stepE (R dir S : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) bad
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) bad (mkSt (rDp R) (mul24 (rPi R) (sPi S))) (Nat.beq (sD S) (rD R)))
      (Bool.rec (motive := fun _ => Nat) bad (mkSt (rD R) (mul24 (rFI R) (sPi S))) (Nat.beq (sD S) (rDp R)))
      (Nat.beq dir (nat_lit 1)))
    (Nat.beq (rJ R) (nat_lit 0))

@[expose] noncomputable def stepU (HB GB TB : Nat → Nat) (nT W Wi : Nat) (isU : Bool) (R dir e S : Nat) : Nat :=
  (fun g t => (fun G Gi TS TP =>
    Bool.rec (motive := fun _ => Nat) bad
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) bad
          (mkSt (rDp R) (Bool.rec (motive := fun _ => Nat) (mul24 (mul24 (rPi R) Gi) TP)
            (mul24 (mul24 (mul24 (rPi R) Gi) TP) Wi) isU))
          (andB (Nat.beq (sD S) (rD R)) (Nat.beq TS (mul24 G (sPi S)))))
        (Bool.rec (motive := fun _ => Nat) bad
          (mkSt (rD R) (Bool.rec (motive := fun _ => Nat) (mul24 (mul24 Gi TS) W) (mul24 Gi TS) isU))
          (andB (Nat.beq (sD S) (rDp R)) (Nat.beq TP (mul24 (mul24 G (rFI R)) (sPi S)))))
        (Nat.beq dir (nat_lit 1)))
      (andB (Nat.blt (nat_lit 0) (rJ R)) (Nat.blt e nT)))
    (mat HB (lo20 g)) (mat HB (hi20 g)) (mat HB (lo20 t)) (mat HB (hi20 t)))
  (e40 GB (Nat.sub (rJ R) (nat_lit 1))) (e40 TB e)

@[expose] noncomputable def stepL (HB GB TB : Nat → Nat) (TL VL nT W Wi c R dir e S : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) bad (stepU HB GB TB nT W Wi true R dir e S) (Nat.beq c VL))
      (stepU HB GB TB nT W Wi false R dir e S) (Nat.beq c TL))
    (stepE R dir S) (Nat.beq c (nat_lit 255))

@[expose] noncomputable def isUL (TL VL c : Nat) : Bool := orB (Nat.beq c TL) (Nat.beq c VL)

@[expose] noncomputable def posBits (TL VL c : Nat) (own : Bool) : Nat :=
  Nat.add (Bool.rec (motive := fun _ => Nat) (nat_lit 21) (nat_lit 0) own)
    (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 17) (isUL TL VL c))

@[expose] noncomputable def walkGo (FB HB GB TB : Nat → Nat) (sh wd LT TL VL NL nT W Wi : Nat) (el : Bool)
    (i Ri ft fd Wd n : Nat) (k : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat)
    (fun _ S A => Nat.lor S (Nat.shiftLeft A (nat_lit 584)))
    (fun k ih J S A => (fun q => (fun c =>
      Bool.rec (motive := fun _ => Nat)
        (ih J (mkSt (sD S) (mul24 (sPi S) (let24 LT c))) A)
        ((fun own => (fun h => (fun R dir =>
            Bool.rec (motive := fun _ => Nat) bad
              (strictN (stepL HB GB TB TL VL nT W Wi c R dir
                  (Bool.rec (motive := fun _ => Nat) (bits J (nat_lit 21) (nat_lit 17)) (bits J (nat_lit 0) (nat_lit 17)) own) S)
                (fun S2 => ih (Nat.shiftRight J (posBits TL VL c own)) S2
                  (Bool.rec (motive := fun _ => Nat) A
                    (mul24 A (Bool.rec (motive := fun _ => Nat) (rN R) (rNI R) (Nat.beq dir (nat_lit 1)))) el)))
              (orB own (Nat.blt h i)))
            (Bool.rec (motive := fun _ => Nat) (rec FB sh wd h) Ri own)
            (Bool.rec (motive := fun _ => Nat) (Nat.land J (nat_lit 1)) fd own))
          (bits J (nat_lit 1) (nat_lit 20)))
         (Nat.beq q ft))
        (notB (isN TL VL NL c)))
      (byte Wd q)) (Nat.sub n (Nat.succ k))) k

@[expose] noncomputable def sI (S : Nat) : Nat := Nat.land S (nat_lit 4294967295)
@[expose] noncomputable def sX (S : Nat) : Nat := Nat.shiftRight S (nat_lit 32)
@[expose] noncomputable def mkS (i nx : Nat) : Nat := Nat.lor i (Nat.shiftLeft nx (nat_lit 32))

@[expose] noncomputable def recOK (ND NO : Nat) (el : Bool) (R : Nat) : Bool :=
  andB (Nat.blt (rD R) ND) (andB (Nat.blt (rDp R) ND) (andB (Nat.ble (rJ R) NO)
    (andB (Nat.beq (mul24 (rPi R) (rFI R)) ident24)
      (Bool.rec (motive := fun _ => Bool) true (Nat.beq (mul24 (rN R) (rNI R)) ident24) el))))

@[expose] noncomputable def treeOK (HB GB : Nat → Nat) (el : Bool) (nx R : Nat) : Bool :=
  andB (Nat.blt (nat_lit 0) (rJ R)) (andB (Nat.beq (rDp R) nx) (andB (Nat.blt (rD R) nx)
    (andB (Nat.beq (rPi R) ident24)
      (andB (Bool.rec (motive := fun _ => Bool) true (Nat.beq (rN R) ident24) el)
        (Bool.rec (motive := fun _ => Bool) true
          (Nat.beq (mat HB (lo20 (e40 GB (Nat.sub (rJ R) (nat_lit 1))))) ident24) (Nat.beq nx (nat_lit 1)))))))

@[expose] noncomputable def axiomOK (HB : Nat → Nat) (nH : Nat) (el : Bool) (Jf R : Nat) : Bool :=
  (fun x b => andB (Nat.beq (rD R) (nat_lit 0)) (andB (Nat.beq (rJ R) (nat_lit 0)) (andB (Nat.beq (rDp R) (nat_lit 0))
    (andB (Nat.blt x nH) (andB (Nat.blt b nH) (andB (Nat.beq (rPi R) (mul24 (mat HB x) (mat HB b)))
      (Bool.rec (motive := fun _ => Bool) true (Nat.beq (rN R) (rFI R)) el)))))))
  (bits Jf (nat_lit 2) (nat_lit 20)) (bits Jf (nat_lit 22) (nat_lit 20))

@[expose] noncomputable def walkOK (FB HB GB TB WD : Nat → Nat) (sh wd LT TL VL NL ND nH nT nW W Wi : Nat)
    (el : Bool) (i Jf R : Nat) : Bool :=
  (fun w D0 x b ft fd => (fun e => (fun n Wd => (fun S0 =>
      andB (Nat.blt w nW) (andB (Nat.blt D0 ND) (andB (Nat.blt x nH) (andB (Nat.blt b nH)
        (andB (Nat.blt ft n) (andB (notB (isN TL VL NL (byte Wd ft)))
          (Nat.beq (walkGo FB HB GB TB sh wd LT TL VL NL nT W Wi el i R ft fd Wd n n
              (Nat.shiftRight Jf (nat_lit 77)) S0 ident24)
            (Nat.lor S0 (Nat.shiftLeft ident24 (nat_lit 584))))))))))
      (mkSt D0 (mul24 (mat HB x) (mat HB b))))
    (bits e (nat_lit 2) (nat_lit 10)) (Nat.shiftRight e (nat_lit 12))) (WD w))
  (bits Jf (nat_lit 2) (nat_lit 16)) (bits Jf (nat_lit 18) (nat_lit 8)) (bits Jf (nat_lit 26) (nat_lit 20))
  (bits Jf (nat_lit 46) (nat_lit 20)) (bits Jf (nat_lit 66) (nat_lit 10)) (bits Jf (nat_lit 76) (nat_lit 1))

@[expose] noncomputable def factStep (FB HB GB TB WD : Nat → Nat) (sh wd LT TL VL NL ND NO nH nT nW W Wi : Nat)
    (el : Bool) (Jf S : Nat) : Nat :=
  (fun i nx R k => Bool.rec (motive := fun _ => Nat) (nat_lit 0)
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat)
          (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (mkS (Nat.succ i) nx)
            (andB (Nat.beq k (nat_lit 2)) (walkOK FB HB GB TB WD sh wd LT TL VL NL ND nH nT nW W Wi el i Jf R)))
          (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (mkS (Nat.succ i) nx) (axiomOK HB nH el Jf R))
          (Nat.beq k (nat_lit 1)))
        (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (mkS (Nat.succ i) (Nat.succ nx)) (treeOK HB GB el nx R))
        (Nat.beq k (nat_lit 0)))
      (andB (Nat.blt (nat_lit 0) S) (recOK ND NO el R)))
    (sI S) (sX S) (rec FB sh wd (sI S)) (Nat.land Jf (nat_lit 3))

@[expose] noncomputable def runChunk (FB HB GB TB WD : Nat → Nat) (sh wd LT TL VL NL ND NO nH nT nW W Wi : Nat)
    (el : Bool) (C S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih J S => (fun L =>
      strictN (factStep FB HB GB TB WD sh wd LT TL VL NL ND NO nH nT nW W Wi el (bits J (nat_lit 12) L) S)
        (ih (Nat.shiftRight J (Nat.add (nat_lit 12) L))))
      (Nat.land J (nat_lit 4095)))
    (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S

@[expose] noncomputable def runFacts (FB HB GB TB WD : Nat → Nat) (sh wd LT TL VL NL ND NO nH nT nW W Wi : Nat)
    (el : Bool) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (runChunk FB HB GB TB WD sh wd LT TL VL NL ND NO nH nT nW W Wi el C S) ih) Cs

@[expose] noncomputable def impOK (FA : Nat → Nat) (shA wdA NFA f : Nat) : Bool :=
  (fun R => andB (Nat.blt f NFA) (andB (Nat.beq (rD R) (nat_lit 1)) (andB (Nat.beq (rJ R) (nat_lit 0))
    (Nat.beq (rDp R) (nat_lit 1))))) (rec FA shA wdA f)

@[expose] noncomputable def hdrOK (HB FA : Nat → Nat) (LT TL VL NL shA wdA NFA h d : Nat) : Bool :=
  (fun k a b H => Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool)
            (Bool.rec (motive := fun _ => Bool) false
              (andB (impOK FA shA wdA NFA a) (Nat.beq H (rFI (rec FA shA wdA a)))) (Nat.beq k (nat_lit 6)))
            (andB (impOK FA shA wdA NFA a) (Nat.beq H (rN (rec FA shA wdA a)))) (Nat.beq k (nat_lit 5)))
          (andB (Nat.blt a h) (Nat.beq (mul24 H (mat HB a)) ident24)) (Nat.beq k (nat_lit 3)))
        (andB (Nat.blt a h) (andB (Nat.blt b h) (Nat.beq H (mul24 (mat HB a) (mat HB b))))) (Nat.beq k (nat_lit 2)))
      (andB (isN TL VL NL a) (Nat.beq H (let24 LT a))) (Nat.beq k (nat_lit 1)))
    (Nat.beq H ident24) (Nat.beq k (nat_lit 0)))
  (Nat.land d (nat_lit 7)) (bits d (nat_lit 3) (nat_lit 20)) (bits d (nat_lit 23) (nat_lit 20)) (mat HB h)

@[expose] noncomputable def runHdr (HB FA : Nat → Nat) (LT TL VL NL shA wdA NFA : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
            (andB (Nat.blt (nat_lit 0) S)
              (hdrOK HB FA LT TL VL NL shA wdA NFA (Nat.sub S (nat_lit 1)) (bits J (nat_lit 0) (nat_lit 43)))))
          (ih2 (Nat.shiftRight J (nat_lit 43))))
        (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S) ih) Cs

@[expose] noncomputable def actOK (NB sel P M Q tau : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (chkAct sel NB P M Q tau) (Nat.beq Q (vecmul P M)) (Nat.beq NB (nat_lit 1))

@[expose] noncomputable def tauBits (NB : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Nat.mul (nat_lit 7) NB) (nat_lit 0) (Nat.beq NB (nat_lit 1))

@[expose] noncomputable def gomOK (HB GB OB : Nat → Nat) (osh owd om NB sel I0 nH j tau : Nat) : Bool :=
  (fun g => andB (Nat.blt (lo20 g) nH) (andB (Nat.blt (hi20 g) nH)
    (andB (actOK NB sel (pt OB osh owd om I0) (mat HB (lo20 g)) (pt OB osh owd om j) tau)
      (andB (Nat.beq (mul24 (mat HB (lo20 g)) (mat HB (hi20 g))) ident24)
        (Bool.rec (motive := fun _ => Bool) (rowsOK NB (pt OB osh owd om j)) true (Nat.beq NB (nat_lit 1)))))))
  (e40 GB j)

@[expose] noncomputable def runGom (HB GB OB : Nat → Nat) (osh owd om NB sel I0 nH : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
            (andB (Nat.blt (nat_lit 0) S)
              (gomOK HB GB OB osh owd om NB sel I0 nH (Nat.sub S (nat_lit 1)) (bits J (nat_lit 0) (tauBits NB)))))
          (ih2 (Nat.shiftRight J (tauBits NB))))
        (Nat.land C (nat_lit 65535)) (Nat.shiftRight C (nat_lit 16)) S) ih) Cs

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

@[expose] noncomputable def segProd (LT TL VL NL Wd o m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ident24
    (fun k acc => (fun c => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (mul24 acc (let24 LT c)) (isN TL VL NL c))
      (byte Wd (Nat.add o k))) m

@[expose] noncomputable def relVisOK (RR : Nat → Nat) (LT TL VL NL NR S P r s ns : Nat) : Bool :=
  (fun e => (fun n => (fun Wd => andB (Nat.blt r NR) (andB (Nat.blt s n) (andB (Nat.ble (Nat.add ns (nat_lit 2)) n)
      (andB (Nat.beq (byte Wd (nat_lit 0)) VL) (andB (Nat.beq (byte Wd (Nat.succ ns)) TL)
        (andB (Nat.beq S (segProd LT TL VL NL Wd (nat_lit 1) ns))
          (Nat.beq (mul24 P (segProd LT TL VL NL Wd (Nat.add ns (nat_lit 2)) (Nat.sub n (Nat.add ns (nat_lit 2))))) ident24)))))))
    (rot (Nat.shiftRight e (nat_lit 12)) n s)) (bits e (nat_lit 2) (nat_lit 10))) (RR r)

@[expose] noncomputable def tOK (HB TB OB RR FA : Nat → Nat) (LT TL VL NL NR nH nT osh owd om NB sel I0 shA wdA NFA e d tau : Nat) : Bool :=
  (fun t k p => (fun S P => andB (Nat.blt (lo20 t) nH) (andB (Nat.blt (hi20 t) nH)
      (andB (Nat.blt (bits d (nat_lit 42) (nat_lit 17)) nT)
        (andB (Nat.beq P (mat HB (lo20 (e40 TB (bits d (nat_lit 42) (nat_lit 17))))))
          (andB (actOK NB sel (pt OB osh owd om I0) S (pt OB osh owd om I0) tau)
            (Bool.rec (motive := fun _ => Bool)
              (Bool.rec (motive := fun _ => Bool)
                (Bool.rec (motive := fun _ => Bool) false
                  (andB (impOK FA shA wdA NFA (bits p (nat_lit 0) (nat_lit 20)))
                    (andB (Nat.beq S (rN (rec FA shA wdA (bits p (nat_lit 0) (nat_lit 20)))))
                      (Nat.beq P (rFI (rec FA shA wdA (bits p (nat_lit 0) (nat_lit 20)))))))
                  (Nat.beq k (nat_lit 2)))
                (relVisOK RR LT TL VL NL NR S P (bits p (nat_lit 0) (nat_lit 8)) (bits p (nat_lit 8) (nat_lit 10))
                  (bits p (nat_lit 18) (nat_lit 10)))
                (Nat.beq k (nat_lit 1)))
              ((fun a b => andB (Nat.blt a e) (andB (Nat.blt b e)
                  (andB (Nat.beq S (mul24 (mat HB (lo20 (e40 TB a))) (mat HB (lo20 (e40 TB b)))))
                    (Nat.beq P (mul24 (mat HB (hi20 (e40 TB a))) (mat HB (hi20 (e40 TB b))))))))
                (bits p (nat_lit 0) (nat_lit 17)) (bits p (nat_lit 17) (nat_lit 17)))
              (Nat.beq k (nat_lit 0))))))))
    (mat HB (lo20 t)) (mat HB (hi20 t)))
  (e40 TB e) (Nat.land d (nat_lit 3)) (bits d (nat_lit 2) (nat_lit 40))

@[expose] noncomputable def runT (HB TB OB RR FA : Nat → Nat) (LT TL VL NL NR nH nT osh owd om NB sel I0 shA wdA NFA : Nat)
    (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
            (andB (Nat.blt (nat_lit 0) S)
              (tOK HB TB OB RR FA LT TL VL NL NR nH nT osh owd om NB sel I0 shA wdA NFA (Nat.sub S (nat_lit 1))
                (bits J (nat_lit 0) (nat_lit 59)) (bits J (nat_lit 59) (tauBits NB)))))
          (ih2 (Nat.shiftRight J (Nat.add (nat_lit 59) (tauBits NB)))))
        (Nat.land C (nat_lit 65535)) (Nat.shiftRight C (nat_lit 16)) S) ih) Cs

@[expose] noncomputable def aliveD (AL D : Nat) : Bool := Nat.blt (nat_lit 0) (Nat.land AL (Nat.shiftLeft (nat_lit 1) D))

@[expose] noncomputable def slotOK (FB OB : Nat → Nat) (sh wd osh owd om NB sel NF AL D w x tau : Nat) : Bool :=
  (fun g => (fun R => andB (Nat.blt g NF)
      (Bool.rec (motive := fun _ => Bool)
        (andB (Nat.beq (rD R) D) (andB (Nat.beq (rJ R) (Nat.succ w)) (aliveD AL (rDp R))))
        (andB (Nat.beq (rDp R) D) (andB (Nat.blt (nat_lit 0) (rJ R)) (andB (aliveD AL (rD R))
          (actOK NB sel (pt OB osh owd om w) (rPi R) (pt OB osh owd om (Nat.sub (rJ R) (nat_lit 1))) tau))))
        (Nat.beq (Nat.land x (nat_lit 1)) (nat_lit 1))))
    (rec FB sh wd g)) (Nat.shiftRight x (nat_lit 1))

@[expose] noncomputable def runCover (FB OB : Nat → Nat) (sh wd osh owd om NB sel NF NO AL : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => (fun D w => (fun nxt =>
            Bool.rec (motive := fun _ => Nat) (nat_lit 0)
              (Bool.rec (motive := fun _ => Nat)
                (strictN nxt (ih2 J))
                ((fun x => (fun tb => strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0) nxt
                      (slotOK FB OB sh wd osh owd om NB sel NF AL D w x (bits J (nat_lit 21) tb)))
                    (ih2 (Nat.shiftRight J (Nat.add (nat_lit 21) tb))))
                  (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (tauBits NB) (Nat.beq (Nat.land x (nat_lit 1)) (nat_lit 1))))
                  (bits J (nat_lit 0) (nat_lit 21)))
                (aliveD AL D))
              (Nat.blt (nat_lit 0) S))
            (Bool.rec (motive := fun _ => Nat) (Nat.add S (nat_lit 1))
              (Nat.add (nat_lit 1) (Nat.shiftLeft (Nat.succ D) (nat_lit 20)))
              (orB (notB (aliveD AL D)) (Nat.beq (Nat.succ w) NO))))
          (Nat.shiftRight (Nat.sub S (nat_lit 1)) (nat_lit 20)) (Nat.land (Nat.sub S (nat_lit 1)) M20))
        (Nat.land C (nat_lit 65535)) (Nat.shiftRight C (nat_lit 16)) S) ih) Cs

@[expose] noncomputable def stabGen (FB : Nat → Nat) (sh wd NF D SG s : Nat) : Nat :=
  (fun g => (fun R => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (rPi R)
      (andB (Nat.blt s (Nat.land SG (nat_lit 31))) (andB (Nat.blt g NF) (andB (Nat.beq (rD R) D)
        (andB (Nat.beq (rJ R) (nat_lit 0)) (Nat.beq (rDp R) D))))))
    (rec FB sh wd g))
  (bits SG (Nat.add (nat_lit 5) (Nat.mul (nat_lit 20) s)) (nat_lit 20))

@[expose] noncomputable def runStab (FB EB : Nat → Nat) (sh wd NF D SG : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
            ((fun k p s => andB (Nat.blt (nat_lit 0) S) (andB (Nat.blt p k)
                (Nat.beq (mat EB k) (mul24 (mat EB p) (stabGen FB sh wd NF D SG s)))))
              (Nat.sub S (nat_lit 1)) (bits J (nat_lit 0) (nat_lit 17)) (bits J (nat_lit 17) (nat_lit 5))))
          (ih2 (Nat.shiftRight J (nat_lit 22))))
        (Nat.land C (nat_lit 65535)) (Nat.shiftRight C (nat_lit 16)) S) ih) Cs

@[expose] noncomputable def stabStart (EB : Nat → Nat) : Bool := Nat.beq (mat EB (nat_lit 0)) ident24

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

@[expose] noncomputable def letterOK (LT LC LI TL VL NL c : Nat) : Bool :=
  andB (Nat.beq (byte LC (byte LI c)) (Nat.xor (byte LC c) (nat_lit 1)))
    (andB (Nat.beq (byte LI (byte LI c)) c) (andB (Nat.blt (byte LI c) NL)
      (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool) false (Nat.beq (byte LC c) (nat_lit 15)) (Nat.beq c VL))
          (Nat.beq (byte LC c) (nat_lit 14)) (Nat.beq c TL))
        (andB (Nat.blt (byte LC c) (nat_lit 14)) (Nat.beq (mul24 (let24 LT c) (let24 LT (byte LI c))) ident24))
        (isN TL VL NL c))))

@[expose] noncomputable def lettersOK (LT LC LI TL VL NL : Nat) : Bool :=
  andB (Nat.blt NL (nat_lit 255)) (andB (Nat.blt TL NL) (andB (Nat.blt VL NL) (andB (notB (Nat.beq TL VL))
    (Nat.rec (motive := fun _ => Bool) true (fun c ih => andB ih (letterOK LT LC LI TL VL NL c)) NL))))

@[expose] noncomputable def lettersSub (LT LC TL VL NL LTB : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun c ih => andB ih
    (Bool.rec (motive := fun _ => Bool) true (Nat.beq (let24 LT c) (let24 LTB (byte LC c))) (isN TL VL NL c))) NL

@[expose] noncomputable def mapW (LC Wd n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (byte LC (byte Wd i)) (Nat.mul (nat_lit 8) i))) n

@[expose] noncomputable def relOK (RR : Nat → Nat) (LT LC TL VL NL RH r : Nat) : Bool :=
  (fun e => (fun n Wd h => andB (Nat.blt h (nat_lit 39))
      (andB (Nat.beq (Nat.add (Nat.mul (nat_lit 4) n) (Nat.shiftLeft (mapW LC Wd n) (nat_lit 12))) (Hsw.sel h))
        (andB (Nat.rec (motive := fun _ => Bool) true (fun i ih => andB ih (Nat.blt (byte Wd i) NL)) n)
          (orB (notB (Nat.rec (motive := fun _ => Bool) true (fun i ih => andB ih (isN TL VL NL (byte Wd i))) n))
            (Nat.beq (segProd LT TL VL NL Wd (nat_lit 0) n) ident24)))))
    (bits e (nat_lit 2) (nat_lit 10)) (Nat.shiftRight e (nat_lit 12)) (byte RH r)) (RR r)

@[expose] noncomputable def relsOK (RR : Nat → Nat) (LT LC TL VL NL RH NR : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun r ih => andB ih (relOK RR LT LC TL VL NL RH r)) NR

@[expose] noncomputable def wordOK (WD RR : Nat → Nat) (LI NL NR WH w : Nat) : Bool :=
  (fun e h => (fun n Wd => andB (Nat.blt h NR)
      (andB (Nat.rec (motive := fun _ => Bool) true (fun i ih => andB ih
          (orB (Nat.blt (byte Wd i) NL) (Nat.beq (byte Wd i) (nat_lit 255)))) n)
        (chkWord LI Wd n (Nat.shiftRight (RR h) (nat_lit 12)) (bits (RR h) (nat_lit 2) (nat_lit 10)))))
    (bits e (nat_lit 2) (nat_lit 10)) (Nat.shiftRight e (nat_lit 12)))
  (WD w) (byte WH w)

@[expose] noncomputable def wordsOK (WD RR : Nat → Nat) (LI NL NR WH nW : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun w ih => andB ih (wordOK WD RR LI NL NR WH w)) nW

@[expose] noncomputable def usqOK (RR : Nat → Nat) (LT LI TL VL NL NR USQ W Wi h : Nat) : Bool :=
  (fun n U => andB (Nat.blt h NR) (andB (Nat.beq W (segProd LT TL VL NL U (nat_lit 0) n))
      (andB (Nat.beq (mul24 W Wi) ident24)
        (andB (Nat.beq (bits (RR h) (nat_lit 2) (nat_lit 10)) (Nat.add n (nat_lit 2)))
          (isRot (Nat.shiftRight (RR h) (nat_lit 12)) (Nat.add n (nat_lit 2))
            (wCat (Nat.lor TL (Nat.shiftLeft TL (nat_lit 8))) (nat_lit 2) (wInv LI U n)))))))
  (bits USQ (nat_lit 2) (nat_lit 10)) (Nat.shiftRight USQ (nat_lit 12))

@[expose] noncomputable def selOK (NB sel : Nat) : Bool :=
  Nat.beq sel (Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 24) NB)) (nat_lit 1)) (nat_lit 16777215))

@[expose] noncomputable def runClass (CB : Nat → Nat) (LT LI TL VL NL : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
            ((fun k p g => andB (Nat.blt (nat_lit 0) S) (andB (Nat.blt p k) (andB (isN TL VL NL g)
                (Nat.beq (mat CB k) (mul24 (mul24 (let24 LT (byte LI g)) (mat CB p)) (let24 LT g))))))
              (Nat.sub S (nat_lit 1)) (bits J (nat_lit 0) (nat_lit 10)) (bits J (nat_lit 10) (nat_lit 4))))
          (ih2 (Nat.shiftRight J (nat_lit 14))))
        (Nat.land C (nat_lit 65535)) (Nat.shiftRight C (nat_lit 16)) S) ih) Cs

@[expose] noncomputable def commOK (LT TL VL NL La : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun c ih => andB ih
    (Bool.rec (motive := fun _ => Bool) true
      (Nat.beq (mul24 (let24 LT c) La) (mul24 La (let24 LT c))) (isN TL VL NL c))) NL

end CFSG.KC.Th.DceS

end
