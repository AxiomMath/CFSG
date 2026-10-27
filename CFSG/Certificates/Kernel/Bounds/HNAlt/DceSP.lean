module

public import CFSG.Certificates.Kernel.Th.Words
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.HNA.DceS

open CFSG.KC.Loop

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false b a
@[expose] noncomputable def orB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) b true a
@[expose] noncomputable def notB (b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false b

@[expose] def M330 : Nat := nat_lit 2187250724783011924372502227117621365353169430893212436425770606409952999199375923223513177023053823
@[expose] def P330 : Nat := nat_lit 2187250724783011924372502227117621365353169430893212436425770606409952999199375923223513177023053824
@[expose] def M20 : Nat := nat_lit 1048575
@[expose] def FULL56 : Nat := nat_lit 72057594037927935
@[expose] def B55 : Nat := nat_lit 36028797018963968
@[expose] def ONEP : Nat := nat_lit 1874235251949363455477671976424043906164305677618497227584793608566452544791402750033552107597733952

@[expose] noncomputable def fld (X i : Nat) : Nat := Nat.land (Nat.shiftRight X (Nat.mul (nat_lit 6) i)) (nat_lit 63)

@[expose] noncomputable def mulP (X Y : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (fld Y (fld X i)) (Nat.mul (nat_lit 6) i))) (nat_lit 55)

@[expose] noncomputable def pmask (X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) B55
    (fun i acc => (fun e => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.lor acc (Nat.shiftLeft (nat_lit 1) e))
        (andB (Nat.blt (nat_lit 0) acc) (andB (Nat.blt e (nat_lit 55))
          (Nat.beq (Nat.land acc (Nat.shiftLeft (nat_lit 1) e)) (nat_lit 0)))))
      (fld X i)) (nat_lit 55)

@[expose] noncomputable def validP (X : Nat) : Bool := andB (Nat.blt X P330) (Nat.beq (pmask X) FULL56)

@[expose] noncomputable def rec (FB : Nat → Nat) (sh wd h : Nat) : Nat :=
  strictN (Nat.shiftRight h sh) (fun k =>
    Nat.shiftRight (FB k) (Nat.mul (Nat.sub h (Nat.shiftLeft k sh)) wd))

@[expose] noncomputable def mat (HB : Nat → Nat) (h : Nat) : Nat :=
  Nat.land (rec HB (nat_lit 6) (nat_lit 330) h) M330

@[expose] noncomputable def e40 (B : Nat → Nat) (j : Nat) : Nat :=
  Nat.land (rec B (nat_lit 8) (nat_lit 40) j) (nat_lit 1099511627775)

@[expose] noncomputable def lo20 (x : Nat) : Nat := Nat.land x M20
@[expose] noncomputable def hi20 (x : Nat) : Nat := Nat.shiftRight x (nat_lit 20)

@[expose] noncomputable def tS (TB : Nat → Nat) (e : Nat) : Nat :=
  Nat.land (rec TB (nat_lit 6) (nat_lit 660) e) M330

@[expose] noncomputable def tP (TB : Nat → Nat) (e : Nat) : Nat :=
  Nat.land (Nat.shiftRight (rec TB (nat_lit 6) (nat_lit 660) e) (nat_lit 330)) M330

@[expose] noncomputable def pt (OB : Nat → Nat) (w : Nat) : Nat :=
  Nat.land (rec OB (nat_lit 6) (nat_lit 12) w) (nat_lit 4095)

@[expose] noncomputable def letP (LT c : Nat) : Nat :=
  Nat.land (Nat.shiftRight LT (Nat.mul c (nat_lit 330))) M330

@[expose] noncomputable def byte (x i : Nat) : Nat := Nat.land (Nat.shiftRight x (Nat.mul (nat_lit 8) i)) (nat_lit 255)

@[expose] noncomputable def bits (J o x : Nat) : Nat :=
  Nat.land (Nat.shiftRight J o) (Nat.sub (Nat.shiftLeft (nat_lit 1) x) (nat_lit 1))

@[expose] noncomputable def p0 (P : Nat) : Nat := Nat.land P (nat_lit 63)
@[expose] noncomputable def p1 (P : Nat) : Nat := Nat.shiftRight P (nat_lit 6)

@[expose] noncomputable def canonP (P : Nat) : Bool :=
  andB (Nat.blt P (nat_lit 4096)) (andB (Nat.blt (p0 P) (p1 P)) (Nat.blt (p1 P) (nat_lit 55)))

@[expose] noncomputable def actOK (P M Q : Nat) : Bool :=
  (fun x y => Nat.beq Q (Bool.rec (motive := fun _ => Nat) (Nat.lor y (Nat.shiftLeft x (nat_lit 6)))
      (Nat.lor x (Nat.shiftLeft y (nat_lit 6))) (Nat.blt x y)))
    (fld M (p0 P)) (fld M (p1 P))

@[expose] noncomputable def rD (R : Nat) : Nat := Nat.land R (nat_lit 65535)
@[expose] noncomputable def rJ (R : Nat) : Nat := Nat.land (Nat.shiftRight R (nat_lit 16)) (nat_lit 65535)
@[expose] noncomputable def rDp (R : Nat) : Nat := Nat.land (Nat.shiftRight R (nat_lit 32)) (nat_lit 65535)
@[expose] noncomputable def rPi (R : Nat) : Nat := Nat.land (Nat.shiftRight R (nat_lit 48)) M330
@[expose] noncomputable def rFI (R : Nat) : Nat := Nat.land (Nat.shiftRight R (nat_lit 378)) M330

@[expose] noncomputable def mkSt (D p : Nat) : Nat := Nat.lor D (Nat.shiftLeft p (nat_lit 16))
@[expose] noncomputable def sD (S : Nat) : Nat := Nat.land S (nat_lit 65535)
@[expose] noncomputable def sPi (S : Nat) : Nat := Nat.shiftRight S (nat_lit 16)
@[expose] def bad : Nat := nat_lit 65535

@[expose] noncomputable def isN (TL VL NL c : Nat) : Bool :=
  andB (Nat.blt c NL) (andB (notB (Nat.beq c TL)) (notB (Nat.beq c VL)))

@[expose] noncomputable def stepE (R dir S : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) bad
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) bad (mkSt (rDp R) (mulP (rPi R) (sPi S))) (Nat.beq (sD S) (rD R)))
      (Bool.rec (motive := fun _ => Nat) bad (mkSt (rD R) (mulP (rFI R) (sPi S))) (Nat.beq (sD S) (rDp R)))
      (Nat.beq dir (nat_lit 1)))
    (Nat.beq (rJ R) (nat_lit 0))

@[expose] noncomputable def stepU (HB GB TB : Nat → Nat) (nT W Wi : Nat) (isU : Bool) (R dir e S : Nat) : Nat :=
  (fun g => (fun G Gi TS TP =>
    Bool.rec (motive := fun _ => Nat) bad
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) bad
          (mkSt (rDp R) (Bool.rec (motive := fun _ => Nat) (mulP (mulP (rPi R) Gi) TP)
            (mulP (mulP (mulP (rPi R) Gi) TP) Wi) isU))
          (andB (Nat.beq (sD S) (rD R)) (Nat.beq TS (mulP G (sPi S)))))
        (Bool.rec (motive := fun _ => Nat) bad
          (mkSt (rD R) (Bool.rec (motive := fun _ => Nat) (mulP (mulP Gi TS) W) (mulP Gi TS) isU))
          (andB (Nat.beq (sD S) (rDp R)) (Nat.beq TP (mulP (mulP G (rFI R)) (sPi S)))))
        (Nat.beq dir (nat_lit 1)))
      (andB (Nat.blt (nat_lit 0) (rJ R)) (Nat.blt e nT)))
    (mat HB (lo20 g)) (mat HB (hi20 g)) (tS TB e) (tP TB e))
  (e40 GB (Nat.sub (rJ R) (nat_lit 1)))

@[expose] noncomputable def stepL (HB GB TB : Nat → Nat) (TL VL nT W Wi c R dir e S : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) bad (stepU HB GB TB nT W Wi true R dir e S) (Nat.beq c VL))
      (stepU HB GB TB nT W Wi false R dir e S) (Nat.beq c TL))
    (stepE R dir S) (Nat.beq c (nat_lit 255))

@[expose] noncomputable def isUL (TL VL c : Nat) : Bool := orB (Nat.beq c TL) (Nat.beq c VL)

@[expose] noncomputable def posBits (TL VL c : Nat) (own : Bool) : Nat :=
  Nat.add (Bool.rec (motive := fun _ => Nat) (nat_lit 21) (nat_lit 0) own)
    (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 19) (isUL TL VL c))

@[expose] noncomputable def walkGo (FB HB GB TB : Nat → Nat) (sh wd LT TL VL NL nT W Wi : Nat)
    (i Ri ft fd Wd n : Nat) (k : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat)
    (fun _ S => S)
    (fun k ih J S => (fun q => (fun c =>
      Bool.rec (motive := fun _ => Nat)
        (ih J (mkSt (sD S) (mulP (sPi S) (letP LT c))))
        ((fun own => (fun h => (fun R dir =>
            Bool.rec (motive := fun _ => Nat) bad
              (strictN (stepL HB GB TB TL VL nT W Wi c R dir
                  (Bool.rec (motive := fun _ => Nat) (bits J (nat_lit 21) (nat_lit 19)) (bits J (nat_lit 0) (nat_lit 19)) own) S)
                (fun S2 => ih (Nat.shiftRight J (posBits TL VL c own)) S2))
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

@[expose] noncomputable def recOK (ND NO R : Nat) : Bool :=
  andB (Nat.blt (rD R) ND) (andB (Nat.blt (rDp R) ND) (andB (Nat.ble (rJ R) NO)
    (andB (validP (rPi R)) (andB (validP (rFI R)) (Nat.beq (mulP (rPi R) (rFI R)) ONEP)))))

@[expose] noncomputable def treeOK (HB GB : Nat → Nat) (nx R : Nat) : Bool :=
  andB (Nat.blt (nat_lit 0) (rJ R)) (andB (Nat.beq (rDp R) nx) (andB (Nat.blt (rD R) nx)
    (andB (Nat.beq (rPi R) ONEP)
      (Bool.rec (motive := fun _ => Bool) true
        (Nat.beq (mat HB (lo20 (e40 GB (Nat.sub (rJ R) (nat_lit 1))))) ONEP) (Nat.beq nx (nat_lit 1))))))

@[expose] noncomputable def axiomOK (HB : Nat → Nat) (nH Jf R : Nat) : Bool :=
  (fun x b => andB (Nat.beq (rD R) (nat_lit 0)) (andB (Nat.beq (rJ R) (nat_lit 0)) (andB (Nat.beq (rDp R) (nat_lit 0))
    (andB (Nat.blt x nH) (andB (Nat.blt b nH) (Nat.beq (rPi R) (mulP (mat HB x) (mat HB b))))))))
  (bits Jf (nat_lit 2) (nat_lit 20)) (bits Jf (nat_lit 22) (nat_lit 20))

@[expose] noncomputable def walkOK (FB HB GB TB WD : Nat → Nat) (sh wd LT TL VL NL ND nH nT nW W Wi : Nat)
    (i Jf R : Nat) : Bool :=
  (fun w D0 x b ft fd => (fun e => (fun n Wd => (fun S0 =>
      andB (Nat.blt w nW) (andB (Nat.blt D0 ND) (andB (Nat.blt x nH) (andB (Nat.blt b nH)
        (andB (Nat.blt ft n) (andB (notB (isN TL VL NL (byte Wd ft)))
          (Nat.beq (walkGo FB HB GB TB sh wd LT TL VL NL nT W Wi i R ft fd Wd n n
              (Nat.shiftRight Jf (nat_lit 85)) S0) S0)))))))
      (mkSt D0 (mulP (mat HB x) (mat HB b))))
    (bits e (nat_lit 2) (nat_lit 10)) (Nat.shiftRight e (nat_lit 12))) (WD w))
  (bits Jf (nat_lit 2) (nat_lit 16)) (bits Jf (nat_lit 18) (nat_lit 16)) (bits Jf (nat_lit 34) (nat_lit 20))
  (bits Jf (nat_lit 54) (nat_lit 20)) (bits Jf (nat_lit 74) (nat_lit 10)) (bits Jf (nat_lit 84) (nat_lit 1))

@[expose] noncomputable def factStep (FB HB GB TB WD : Nat → Nat) (sh wd LT TL VL NL ND NO nH nT nW W Wi : Nat)
    (Jf S : Nat) : Nat :=
  (fun i nx R k => Bool.rec (motive := fun _ => Nat) (nat_lit 0)
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat)
          (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (mkS (Nat.succ i) nx)
            (andB (Nat.beq k (nat_lit 2)) (walkOK FB HB GB TB WD sh wd LT TL VL NL ND nH nT nW W Wi i Jf R)))
          (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (mkS (Nat.succ i) nx) (axiomOK HB nH Jf R))
          (Nat.beq k (nat_lit 1)))
        (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (mkS (Nat.succ i) (Nat.succ nx)) (treeOK HB GB nx R))
        (Nat.beq k (nat_lit 0)))
      (andB (Nat.blt (nat_lit 0) S) (recOK ND NO R)))
    (sI S) (sX S) (rec FB sh wd (sI S)) (Nat.land Jf (nat_lit 3))

@[expose] noncomputable def runChunk (FB HB GB TB WD : Nat → Nat) (sh wd LT TL VL NL ND NO nH nT nW W Wi : Nat)
    (C S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih J S => (fun L =>
      strictN (factStep FB HB GB TB WD sh wd LT TL VL NL ND NO nH nT nW W Wi (bits J (nat_lit 12) L) S)
        (ih (Nat.shiftRight J (Nat.add (nat_lit 12) L))))
      (Nat.land J (nat_lit 4095)))
    (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S

@[expose] noncomputable def runFacts (FB HB GB TB WD : Nat → Nat) (sh wd LT TL VL NL ND NO nH nT nW W Wi : Nat)
    (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (runChunk FB HB GB TB WD sh wd LT TL VL NL ND NO nH nT nW W Wi C S) ih) Cs

@[expose] noncomputable def hdrOK (HB : Nat → Nat) (LT TL VL NL h d : Nat) : Bool :=
  (fun k a b H => Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false
          (andB (Nat.blt a h) (andB (validP H) (Nat.beq (mulP H (mat HB a)) ONEP))) (Nat.beq k (nat_lit 3)))
        (andB (Nat.blt a h) (andB (Nat.blt b h) (Nat.beq H (mulP (mat HB a) (mat HB b))))) (Nat.beq k (nat_lit 2)))
      (andB (isN TL VL NL a) (Nat.beq H (letP LT a))) (Nat.beq k (nat_lit 1)))
    (Nat.beq H ONEP) (Nat.beq k (nat_lit 0)))
  (Nat.land d (nat_lit 7)) (bits d (nat_lit 3) (nat_lit 20)) (bits d (nat_lit 23) (nat_lit 20)) (mat HB h)

@[expose] noncomputable def runHdr (HB : Nat → Nat) (LT TL VL NL : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
            (andB (Nat.blt (nat_lit 0) S)
              (hdrOK HB LT TL VL NL (Nat.sub S (nat_lit 1)) (bits J (nat_lit 0) (nat_lit 43)))))
          (ih2 (Nat.shiftRight J (nat_lit 43))))
        (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S) ih) Cs

@[expose] noncomputable def gomOK (HB GB OB : Nat → Nat) (I0 nH j : Nat) : Bool :=
  (fun g => andB (Nat.blt (lo20 g) nH) (andB (Nat.blt (hi20 g) nH)
    (andB (actOK (pt OB I0) (mat HB (lo20 g)) (pt OB j))
      (andB (Nat.beq (mulP (mat HB (lo20 g)) (mat HB (hi20 g))) ONEP) (canonP (pt OB j))))))
  (e40 GB j)

@[expose] noncomputable def runGom (HB GB OB : Nat → Nat) (I0 nH : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat) (fun S => S)
        (fun _ ih2 S => strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
            (andB (Nat.blt (nat_lit 0) S) (gomOK HB GB OB I0 nH (Nat.sub S (nat_lit 1)))))
          ih2)
        C S) ih) Cs

@[expose] noncomputable def runSorted (get : Nat → Nat) (qb m : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => (fun q => strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
            (Nat.lor (Nat.succ (Nat.land S M20)) (Nat.shiftLeft (get q) (nat_lit 20)))
            (andB (Nat.blt (nat_lit 0) S) (andB (Nat.blt q m) (Nat.blt (Nat.shiftRight S (nat_lit 20)) (get q)))))
          (ih2 (Nat.shiftRight J qb))) (bits J (nat_lit 0) qb))
        (Nat.land C (nat_lit 65535)) (Nat.shiftRight C (nat_lit 16)) S) ih) Cs

@[expose] noncomputable def sortedCount (S : Nat) : Nat := Nat.sub (Nat.land S M20) (nat_lit 1)

@[expose] noncomputable def segProd (LT TL VL NL Wd o m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ONEP
    (fun k acc => (fun c => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (mulP acc (letP LT c)) (isN TL VL NL c))
      (byte Wd (Nat.add o k))) m

@[expose] noncomputable def relVisOK (RR : Nat → Nat) (LT TL VL NL NR S P r s ns : Nat) : Bool :=
  (fun e => (fun n => (fun Wd => andB (Nat.blt r NR) (andB (Nat.blt s n) (andB (Nat.ble (Nat.add ns (nat_lit 2)) n)
      (andB (Nat.beq (byte Wd (nat_lit 0)) VL) (andB (Nat.beq (byte Wd (Nat.succ ns)) TL)
        (andB (Nat.beq S (segProd LT TL VL NL Wd (nat_lit 1) ns))
          (Nat.beq (mulP P (segProd LT TL VL NL Wd (Nat.add ns (nat_lit 2)) (Nat.sub n (Nat.add ns (nat_lit 2))))) ONEP)))))))
    (CFSG.KC.Th.rot (Nat.shiftRight e (nat_lit 12)) n s)) (bits e (nat_lit 2) (nat_lit 10))) (RR r)

@[expose] noncomputable def tOK (TB OB RR : Nat → Nat) (LT TL VL NL NR nT I0 e d : Nat) : Bool :=
  (fun k p ep => (fun S P => andB (validP S) (andB (validP P)
      (andB (Nat.blt ep nT) (andB (Nat.beq P (tS TB ep))
        (Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool) false
            (andB (relVisOK RR LT TL VL NL NR S P (bits p (nat_lit 0) (nat_lit 8)) (bits p (nat_lit 8) (nat_lit 10))
                (bits p (nat_lit 18) (nat_lit 10)))
              (actOK (pt OB I0) S (pt OB I0)))
            (Nat.beq k (nat_lit 1)))
          ((fun a b => andB (Nat.blt a e) (andB (Nat.blt b e)
              (andB (Nat.beq S (mulP (tS TB a) (tS TB b))) (Nat.beq P (mulP (tP TB a) (tP TB b))))))
            (bits p (nat_lit 0) (nat_lit 19)) (bits p (nat_lit 19) (nat_lit 19)))
          (Nat.beq k (nat_lit 0)))))))
    (tS TB e) (tP TB e))
  (Nat.land d (nat_lit 3)) (bits d (nat_lit 2) (nat_lit 38)) (bits d (nat_lit 40) (nat_lit 19))

@[expose] noncomputable def runT (TB OB RR : Nat → Nat) (LT TL VL NL NR nT I0 : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
            (andB (Nat.blt (nat_lit 0) S)
              (tOK TB OB RR LT TL VL NL NR nT I0 (Nat.sub S (nat_lit 1)) (bits J (nat_lit 0) (nat_lit 59)))))
          (ih2 (Nat.shiftRight J (nat_lit 59))))
        (Nat.land C (nat_lit 65535)) (Nat.shiftRight C (nat_lit 16)) S) ih) Cs

@[expose] noncomputable def aliveD (AL D : Nat) : Bool := Nat.blt (nat_lit 0) (Nat.land AL (Nat.shiftLeft (nat_lit 1) D))

@[expose] noncomputable def slotOK (FB OB : Nat → Nat) (sh wd NF AL D w x : Nat) : Bool :=
  (fun g => (fun R => andB (Nat.blt g NF)
      (Bool.rec (motive := fun _ => Bool)
        (andB (Nat.beq (rD R) D) (andB (Nat.beq (rJ R) (Nat.succ w)) (aliveD AL (rDp R))))
        (andB (Nat.beq (rDp R) D) (andB (Nat.blt (nat_lit 0) (rJ R)) (andB (aliveD AL (rD R))
          (actOK (pt OB w) (rPi R) (pt OB (Nat.sub (rJ R) (nat_lit 1)))))))
        (Nat.beq (Nat.land x (nat_lit 1)) (nat_lit 1))))
    (rec FB sh wd g)) (Nat.shiftRight x (nat_lit 1))

@[expose] noncomputable def runCover (FB OB : Nat → Nat) (sh wd NF NO AL : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => (fun D w => (fun nxt =>
            Bool.rec (motive := fun _ => Nat) (nat_lit 0)
              (Bool.rec (motive := fun _ => Nat)
                (strictN nxt (ih2 J))
                (strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0) nxt
                    (slotOK FB OB sh wd NF AL D w (bits J (nat_lit 0) (nat_lit 21))))
                  (ih2 (Nat.shiftRight J (nat_lit 21))))
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
                (Nat.beq (mat EB k) (mulP (mat EB p) (stabGen FB sh wd NF D SG s)))))
              (Nat.sub S (nat_lit 1)) (bits J (nat_lit 0) (nat_lit 19)) (bits J (nat_lit 19) (nat_lit 5))))
          (ih2 (Nat.shiftRight J (nat_lit 24))))
        (Nat.land C (nat_lit 65535)) (Nat.shiftRight C (nat_lit 16)) S) ih) Cs

@[expose] noncomputable def stabStart (EB : Nat → Nat) : Bool := Nat.beq (mat EB (nat_lit 0)) ONEP

@[expose] noncomputable def sumOK (AL MD ND NORD SUM : Nat) : Bool :=
  andB (aliveD AL (nat_lit 0)) (andB (Nat.blt AL (Nat.shiftLeft (nat_lit 1) ND))
    ((fun r => andB (Nat.blt (nat_lit 0) r) (Nat.beq (Nat.sub r (nat_lit 1)) SUM))
      (Nat.rec (motive := fun _ => Nat) (nat_lit 2)
        (fun D acc => (fun m => Bool.rec (motive := fun _ => Nat) acc
            (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.add acc (Nat.div NORD m))
              (andB (Nat.blt (nat_lit 0) acc) (andB (Nat.blt (nat_lit 0) m) (Nat.beq (Nat.mod NORD m) (nat_lit 0)))))
            (andB (aliveD AL D) (notB (Nat.beq D (nat_lit 0)))))
          (bits MD (Nat.mul (nat_lit 24) D) (nat_lit 24)))
        ND)))

@[expose] noncomputable def letterOK (LT LI TL VL NL c : Nat) : Bool :=
  andB (Nat.beq (byte LI (byte LI c)) c) (andB (Nat.blt (byte LI c) NL)
    (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) true (Nat.beq (byte LI c) VL) (Nat.beq c TL))
      (andB (validP (letP LT c)) (Nat.beq (mulP (letP LT c) (letP LT (byte LI c))) ONEP))
      (isN TL VL NL c)))

@[expose] noncomputable def lettersOK (LT LI TL VL NL : Nat) : Bool :=
  andB (Nat.blt NL (nat_lit 255)) (andB (Nat.blt TL NL) (andB (Nat.blt VL NL)
    (Nat.rec (motive := fun _ => Bool) true (fun c ih => andB ih (letterOK LT LI TL VL NL c)) NL)))

@[expose] noncomputable def relOK (RR : Nat → Nat) (LT TL VL NL r : Nat) : Bool :=
  (fun e => (fun n Wd =>
      andB (Nat.rec (motive := fun _ => Bool) true (fun i ih => andB ih (Nat.blt (byte Wd i) NL)) n)
        (orB (notB (Nat.rec (motive := fun _ => Bool) true (fun i ih => andB ih (isN TL VL NL (byte Wd i))) n))
          (Nat.beq (segProd LT TL VL NL Wd (nat_lit 0) n) ONEP)))
    (bits e (nat_lit 2) (nat_lit 10)) (Nat.shiftRight e (nat_lit 12))) (RR r)

@[expose] noncomputable def relsOK (RR : Nat → Nat) (LT TL VL NL NR : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun r ih => andB ih (relOK RR LT TL VL NL r)) NR

@[expose] noncomputable def wordOK (WD RR : Nat → Nat) (LI NL NR WH w : Nat) : Bool :=
  (fun e h => (fun n Wd => andB (Nat.blt h NR)
      (andB (Nat.rec (motive := fun _ => Bool) true (fun i ih => andB ih
          (orB (Nat.blt (byte Wd i) NL) (Nat.beq (byte Wd i) (nat_lit 255)))) n)
        (CFSG.KC.Th.chkWord LI Wd n (Nat.shiftRight (RR h) (nat_lit 12)) (bits (RR h) (nat_lit 2) (nat_lit 10)))))
    (bits e (nat_lit 2) (nat_lit 10)) (Nat.shiftRight e (nat_lit 12)))
  (WD w) (byte WH w)

@[expose] noncomputable def wordsOK (WD RR : Nat → Nat) (LI NL NR WH nW : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun w ih => andB ih (wordOK WD RR LI NL NR WH w)) nW

@[expose] noncomputable def usqOK (RR : Nat → Nat) (LT LI TL VL NL NR USQ W Wi h : Nat) : Bool :=
  (fun n U => andB (Nat.blt h NR) (andB (Nat.beq W (segProd LT TL VL NL U (nat_lit 0) n))
      (andB (validP Wi) (andB (Nat.beq (mulP W Wi) ONEP)
        (andB (Nat.beq (bits (RR h) (nat_lit 2) (nat_lit 10)) (Nat.add n (nat_lit 2)))
          (CFSG.KC.Th.isRot (Nat.shiftRight (RR h) (nat_lit 12)) (Nat.add n (nat_lit 2))
            (CFSG.KC.Th.wCat (Nat.lor TL (Nat.shiftLeft TL (nat_lit 8))) (nat_lit 2) (CFSG.KC.Th.wInv LI U n))))))))
  (bits USQ (nat_lit 2) (nat_lit 10)) (Nat.shiftRight USQ (nat_lit 12))

end CFSG.KC.HNA.DceS

end
