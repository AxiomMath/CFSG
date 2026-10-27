module

public import CFSG.Certificates.Kernel.J4.Dce
public import CFSG.Certificates.Kernel.J4.Words
public import CFSG.Certificates.Kernel.J4.Orb
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KJ4.S

open CFSG.KJ4 CFSG.KC.Loop

@[expose] noncomputable def letB (v : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) v

@[expose] noncomputable def strictT {α : Type} (y : Nat) (k : Nat → α) : α :=
  Nat.rec (motive := fun _ => α) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def mulF (A B : Nat) : Nat := strictN A (fun a => strictN B (fun b => mul12 a b))

@[expose] noncomputable def chkPtF (P g Q h : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) (chkPt (nat_lit 0) g Q h) (fun p _ =>
    Nat.rec (motive := fun _ => Bool) (chkPt (Nat.succ p) (nat_lit 0) Q h) (fun g' _ =>
      Nat.rec (motive := fun _ => Bool) (chkPt (Nat.succ p) (Nat.succ g') (nat_lit 0) h) (fun q _ =>
        chkPt (Nat.succ p) (Nat.succ g') (Nat.succ q) h) Q) g) P

@[expose] noncomputable def chkOmF (TH O H h : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) (chkOm TH (nat_lit 0) H h) (fun o _ =>
    Nat.rec (motive := fun _ => Bool) (chkOm TH (Nat.succ o) (nat_lit 0) h) (fun x _ =>
      chkOm TH (Nat.succ o) (Nat.succ x) h) H) O

@[expose] noncomputable def rngAll (a b hi : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun h ih => andB
    (Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      andB ((fun i => Bool.rec (motive := fun _ => Bool) true (f i) (Nat.blt i b))
        (Nat.add a (Nat.add (Nat.shiftLeft h (nat_lit 6)) l))) ih2) (nat_lit 64)) ih) hi

@[expose] noncomputable def letsBelow (w n m : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i acc => andB acc (Nat.blt (wLet w i) m)) n

@[expose] def FAIL : Nat := nat_lit 2147483648
@[expose] def mask32 : Nat := nat_lit 4294967295
@[expose] noncomputable def cIdx (st : Nat) : Nat := Nat.land st mask32
@[expose] noncomputable def cNd (st : Nat) : Nat := Nat.land (Nat.shiftRight st (nat_lit 32)) mask32
@[expose] noncomputable def mkC (k nd : Nat) : Nat := Nat.lor k (Nat.shiftLeft nd (nat_lit 32))

@[expose] noncomputable def fPiI (F : Nat) : Nat := Nat.land (Nat.shiftRight F (nat_lit 212)) mask144
@[expose] noncomputable def fNs (F : Nat) : Nat := Nat.land (Nat.shiftRight F (nat_lit 356)) mask144
@[expose] noncomputable def fNIs (F : Nat) : Nat := Nat.shiftRight F (nat_lit 500)

@[expose] noncomputable def hMat (H : Nat) : Nat := Nat.land H mask144
@[expose] noncomputable def hInv (H : Nat) : Nat := Nat.land (Nat.shiftRight H (nat_lit 144)) mask144
@[expose] noncomputable def hKind (H : Nat) : Nat := Nat.land (Nat.shiftRight H (nat_lit 288)) (nat_lit 15)
@[expose] noncomputable def hA (H : Nat) : Nat := Nat.land (Nat.shiftRight H (nat_lit 292)) (nat_lit 65535)
@[expose] noncomputable def hB (H : Nat) : Nat := Nat.land (Nat.shiftRight H (nat_lit 308)) (nat_lit 65535)

@[expose] noncomputable def oH (O : Nat) : Nat := Nat.land (Nat.shiftRight O (nat_lit 340)) (nat_lit 65535)
@[expose] noncomputable def oS (O : Nat) : Nat := Nat.shiftRight O (nat_lit 356)
@[expose] noncomputable def oGi' (O : Nat) : Nat := Nat.land (Nat.shiftRight O (nat_lit 196)) mask144

@[expose] noncomputable def lPar (L : Nat) : Nat := Nat.land (Nat.shiftRight L (nat_lit 288)) (nat_lit 65535)
@[expose] noncomputable def lK (L : Nat) : Nat := Nat.land (Nat.shiftRight L (nat_lit 304)) (nat_lit 65535)
@[expose] noncomputable def lS (L : Nat) : Nat := Nat.shiftRight L (nat_lit 320)
@[expose] noncomputable def lP' (L : Nat) : Nat := Nat.land (Nat.shiftRight L (nat_lit 144)) mask144

@[expose] noncomputable def cC (C : Nat) : Nat := Nat.land C mask144
@[expose] noncomputable def cCI (C : Nat) : Nat := Nat.land (Nat.shiftRight C (nat_lit 144)) mask144
@[expose] noncomputable def cBT (C : Nat) : Nat := Nat.land (Nat.shiftRight C (nat_lit 288)) mask144
@[expose] noncomputable def cBP (C : Nat) : Nat := Nat.land (Nat.shiftRight C (nat_lit 432)) mask144
@[expose] noncomputable def cS (C : Nat) : Nat := Nat.land (Nat.shiftRight C (nat_lit 576)) (nat_lit 65535)
@[expose] noncomputable def cN (C : Nat) : Nat := Nat.land (Nat.shiftRight C (nat_lit 592)) (nat_lit 65535)
@[expose] noncomputable def cW (C : Nat) : Nat := Nat.shiftRight C (nat_lit 608)

@[expose] noncomputable def wN (W : Nat) : Nat := Nat.land W (nat_lit 65535)
@[expose] noncomputable def wR (W : Nat) : Nat := Nat.land (Nat.shiftRight W (nat_lit 16)) (nat_lit 65535)
@[expose] noncomputable def wW (W : Nat) : Nat := Nat.shiftRight W (nat_lit 32)

@[expose] noncomputable def wFits (w n : Nat) : Bool := Nat.blt w (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 8) n))

@[expose] noncomputable def hOK (HT : Nat → Nat) (LET nl R1 R2 h : Nat) : Bool :=
  letB (HT h) (fun H =>
    andB (Nat.beq (mulF (hMat H) (hInv H)) ident12)
    (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool)
            (andB (Nat.beq (hKind H) (nat_lit 4))
              (andB (Nat.blt (nat_lit 0) (hMat H)) (orB (Nat.beq (hMat H) R1) (Nat.beq (hMat H) R2))))
            (andB (Nat.blt (hA H) h) (Nat.beq (mulF (hMat H) (hMat (HT (hA H)))) ident12))
            (Nat.beq (hKind H) (nat_lit 3)))
          (andB (Nat.blt (hA H) h) (andB (Nat.blt (hB H) h)
            (Nat.beq (hMat H) (mulF (hMat (HT (hA H))) (hMat (HT (hB H)))))))
          (Nat.beq (hKind H) (nat_lit 2)))
        (andB (Nat.blt (hA H) nl) (Nat.beq (hMat H) (letMat LET (hA H))))
        (Nat.beq (hKind H) (nat_lit 1)))
      (Nat.beq (hMat H) ident12)
      (Nat.beq (hKind H) (nat_lit 0))))

@[expose] noncomputable def ptAt (PT : Nat → Nat) (i : Nat) : Bool :=
  andB (ptOK (PT i))
    (Bool.rec (motive := fun _ => Bool) (Nat.blt (PT (Nat.sub i (nat_lit 1))) (PT i)) true (Nat.beq i (nat_lit 0)))

@[expose] noncomputable def oBase (O : Nat) : Nat := Nat.land O (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 340)) (nat_lit 1))

@[expose] noncomputable def omOKm (HT : Nat → Nat) (TH j O : Nat) : Bool :=
  orB (Nat.beq O (nat_lit 0))
    (andB (Nat.beq (oJ O) (Nat.succ j)) (chkOmF TH (oBase O) (hMat (HT (oH O))) (oS O)))

@[expose] noncomputable def omOK (HT PT : Nat → Nat) (TH j O : Nat) : Bool :=
  orB (Nat.beq O (nat_lit 0))
    (andB (Nat.beq (oJ O) (Nat.succ j)) (andB (Nat.beq (oP O) (PT j))
      (chkOmF TH (oBase O) (hMat (HT (oH O))) (oS O))))

@[expose] noncomputable def conjOK (CT : Nat → Nat) (LET TH TR PS k : Nat) : Bool :=
  letB (CT k) (fun C =>
    andB (letsBelow (cW C) (cN C) (nat_lit 4)) (andB (wFits (cW C) (cN C))
    (andB (chkEval LET (cW C) (cN C) (cC C)) (andB (chkLin (cC C)) (andB (chkPtF TH (cC C) TH (cS C))
    (andB (Nat.beq (mulF (cC C) (cCI C)) ident12)
    (andB (Nat.beq (cBT C) (mulF (mul12 (cCI C) TR) (cC C)))
      (Nat.beq (cBP C) (mulF (mul12 (cCI C) PS) (cC C))))))))))

@[expose] noncomputable def lamOK (LT CT : Nat → Nat) (TH e : Nat) : Bool :=
  letB (LT e) (fun L =>
    Bool.rec (motive := fun _ => Bool)
      (andB (Nat.blt (lPar L) e) (andB (Nat.blt (lK L) (nat_lit 9))
        (andB (Nat.beq (lamT L) (mulF (lamT (LT (lPar L))) (cBT (CT (lK L)))))
        (andB (Nat.beq (lP' L) (mulF (lP' (LT (lPar L))) (cBP (CT (lK L)))))
        (andB (chkTrans (lamT L)) (chkPtF TH (lamT L) TH (lS L)))))))
      (andB (Nat.beq (lamT L) ident12) (Nat.beq (lP' L) ident12))
      (Nat.beq e (nat_lit 0)))

@[expose] noncomputable def colOf (A : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun r acc => Nat.lor acc
    (Nat.shiftLeft (Nat.land (Nat.shiftRight A (Nat.add (Nat.mul (nat_lit 12) r) (nat_lit 11))) (nat_lit 1)) r)) (nat_lit 11)

@[expose] noncomputable def lamCols (LT : Nat → Nat) (m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun e BM =>
    strictN BM (fun B => strictN (colOf (lamT (LT e))) (fun c =>
      Bool.rec (motive := fun _ => Nat) (Nat.lor B (Nat.shiftLeft (nat_lit 1) (nat_lit 2048)))
        (Nat.lor B (Nat.shiftLeft (nat_lit 1) c))
        (Nat.beq (Nat.land B (Nat.shiftLeft (nat_lit 1) c)) (nat_lit 0))))) m

@[expose] noncomputable def wordOK (RT : Nat → Nat) (INV W : Nat) : Bool :=
  letB (RT (wR W)) (fun R =>
    andB (wFits (wW W) (wN W)) (chkWord INV (wW W) (wN W) (wW R) (wN R)))

@[expose] noncomputable def relOK (LET R : Nat) : Bool :=
  andB (wFits (wW R) (wN R))
    ((fun M => orB (Nat.beq M ident12) (Nat.beq M (nat_lit 0))) (evalW LET (wW R) (wN R)))

@[expose] def invKR : Nat := nat_lit 1413989166940161

@[expose] noncomputable def omAt (HT PT OT : Nat → Nat) (TH j : Nat) : Bool := omOK HT PT TH j (OT j)
@[expose] noncomputable def omAtm (HT OT : Nat → Nat) (TH j : Nat) : Bool := omOKm HT TH j (OT j)
@[expose] noncomputable def wordAt (RT WT : Nat → Nat) (INV w : Nat) : Bool := wordOK RT INV (WT w)
@[expose] noncomputable def relAt (RT : Nat → Nat) (LET r : Nat) : Bool := relOK LET (RT r)
@[expose] noncomputable def rzAt (RZT : Nat → Nat) (LET i : Nat) : Bool :=
  andB (wFits (wW (RZT i)) (wN (RZT i))) (chkEval LET (wW (RZT i)) (wN (RZT i)) ident12)

@[expose] def dWord : Nat := nat_lit 0x00030002000200020002

@[expose] noncomputable def zWord (INV : Nat) : Nat :=
  (fun u => Nat.lor (nat_lit 66) (Nat.shiftLeft (wCat (wCat u (nat_lit 22) u) (nat_lit 44) u) (nat_lit 32)))
    (wCat (wCat (wCat (nat_lit 2) (nat_lit 1) (wInv INV dWord (nat_lit 10))) (nat_lit 11) (nat_lit 4)) (nat_lit 12) dWord)

@[expose] noncomputable def linkAt (RZT TW : Nat → Nat) (INV ZW i : Nat) : Bool :=
  letB (TW i) (fun T => letB (RZT i) (fun R =>
    andB (wFits (wW T) (wN T)) (andB (wFits (wW R) (wN R))
      (chkSubstRed INV (wW R) (wN R) (wW ZW) (wInv INV (wW ZW) (wN ZW)) (wN ZW) (wW T) (wN T)))))

@[expose] noncomputable def psiWord (INV PA PB : Nat) : Nat :=
  (fun nA nB => Nat.lor (Nat.add (Nat.add nA nB) (nat_lit 2)) (Nat.shiftLeft
    (wCat (wCat (wCat (nat_lit 4) (nat_lit 1) (wW PA)) (Nat.succ nA) (nat_lit 4)) (Nat.add nA (nat_lit 2))
      (wInv INV (wW PB) nB)) (nat_lit 32)))
  (wN PA) (wN PB)

@[expose] noncomputable def psiGenOK (RT HT : Nat → Nat) (LET INV TH r sw sn pw pn sH h : Nat) : Bool :=
  letB (hMat (HT sH)) (fun H =>
    andB (chkPsiRel INV (nat_lit 4) sw sn pw pn (wW (RT r)) (wN (RT r)))
    (andB (chkEval LET sw sn H) (andB (chkLin H) (andB (chkPtF TH H TH h) (chkEval LET pw pn H)))))

@[expose] noncomputable def recOK (F k ND NOM : Nat) : Bool :=
  andB (Nat.beq (fIdx F) k) (andB (Nat.blt (fD F) ND) (andB (Nat.blt (fDp F) ND)
    (andB (Nat.ble (fJ F) NOM) (Nat.beq (mulF (fPi F) (fPiI F)) ident12))))

@[expose] noncomputable def recOKm (F k ND NOM : Nat) : Bool :=
  andB (recOK F k ND NOM) (Nat.beq (mulF (fNs F) (fNIs F)) ident12)

@[expose] noncomputable def jTree (FT : Nat → Nat) (m : Bool) (ND NOM st0 : Nat) : Nat :=
  strictN st0 (fun st => strictN (FT (cIdx st)) (fun F =>
    Bool.rec (motive := fun _ => Nat) FAIL (mkC (Nat.succ (cIdx st)) (Nat.succ (cNd st)))
      (andB (Bool.rec (motive := fun _ => Bool) (recOK F (cIdx st) ND NOM) (recOKm F (cIdx st) ND NOM) m)
      (andB (Nat.blt (nat_lit 0) (fJ F)) (andB (Nat.beq (fDp F) (cNd st)) (andB (Nat.blt (fD F) (cNd st))
      (andB (Nat.beq (fPi F) ident12)
        (Bool.rec (motive := fun _ => Bool) true (Nat.beq (fNs F) ident12) m))))))))

@[expose] noncomputable def jAx (FT HT : Nat → Nat) (m : Bool) (ND NOM a b st0 : Nat) : Nat :=
  strictN st0 (fun st => strictN (FT (cIdx st)) (fun F =>
    Bool.rec (motive := fun _ => Nat) FAIL (mkC (Nat.succ (cIdx st)) (cNd st))
      (andB (Bool.rec (motive := fun _ => Bool) (recOK F (cIdx st) ND NOM) (recOKm F (cIdx st) ND NOM) m)
      (andB (Nat.beq (fD F) (nat_lit 0)) (andB (Nat.beq (fJ F) (nat_lit 0)) (andB (Nat.beq (fDp F) (nat_lit 0))
      (andB (Nat.beq (fPi F) (mulF (hInv (HT a)) (hMat (HT b))))
        (Bool.rec (motive := fun _ => Bool) true (Nat.beq (fNs F) (fPiI F)) m))))))))

@[expose] noncomputable def dD (d : Nat) : Nat := Nat.land d (nat_lit 65535)
@[expose] noncomputable def dD0 (d : Nat) : Nat := Nat.land (Nat.shiftRight d (nat_lit 16)) (nat_lit 65535)
@[expose] noncomputable def dK (d : Nat) : Nat := Nat.land (Nat.shiftRight d (nat_lit 32)) mask32
@[expose] noncomputable def dNd (d : Nat) : Nat := Nat.land (Nat.shiftRight d (nat_lit 64)) mask32
@[expose] noncomputable def dP0 (d : Nat) : Nat := Nat.shiftRight d (nat_lit 96)
@[expose] noncomputable def setD (d D : Nat) : Nat := Nat.lor (Nat.shiftLeft (Nat.shiftRight d (nat_lit 16)) (nat_lit 16)) D

@[expose] noncomputable def mkD (D0 K nd P0 : Nat) : Nat :=
  Nat.lor D0 (Nat.lor (Nat.shiftLeft D0 (nat_lit 16)) (Nat.lor (Nat.shiftLeft K (nat_lit 32))
    (Nat.lor (Nat.shiftLeft nd (nat_lit 64)) (Nat.shiftLeft P0 (nat_lit 96)))))

@[expose] noncomputable def refS (K S g c : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Nat.blt g K)
    (andB (Nat.beq g K) (Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0))) (Nat.beq S (nat_lit 1))

@[expose] noncomputable def hdrIn (HT : Nat → Nat) (a b : Nat) : Bool :=
  andB (Nat.blt (nat_lit 0) (HT a)) (Nat.blt (nat_lit 0) (HT b))

@[expose] noncomputable def stS (FT HT WT : Nat → Nat) (ND NOM a b D0 w st0 : Nat) : St :=
  strictT st0 (fun st => Bool.rec (motive := fun _ => St) bad
    (strictT (mulF (hInv (HT a)) (hMat (HT b))) (fun P0 =>
      strictT (WT w) (fun W =>
        Prod.mk (mkD D0 (cIdx st) (cNd st) P0) (Prod.mk P0 (wInit (wW W) (wN W))))))
    (andB (hdrIn HT a b) (andB (Nat.blt D0 ND) (recOK (FT (cIdx st)) (cIdx st) ND NOM))))

@[expose] noncomputable def sNs (LET : Nat) (s : St) : St :=
  Prod.rec (motive := fun _ => St) (fun d pc => Prod.rec (motive := fun _ => St) (fun p c =>
    Bool.rec bad (Prod.mk d (Prod.mk (mul12 p (letMat LET (letAt c))) (adv c (nat_lit 1) (nat_lit 0))))
      (Nat.blt (letAt c) (nat_lit 4))) pc) s

@[expose] noncomputable def sEfs (FT : Nat → Nat) (S g : Nat) (s : St) : St :=
  Prod.rec (motive := fun _ => St) (fun d pc => Prod.rec (motive := fun _ => St) (fun p c =>
    (fun F => Bool.rec bad (Prod.mk (setD d (fDp F)) (Prod.mk (mulF (fPi F) p) (adv c (nat_lit 1) S)))
      (andB (Nat.beq (letAt c) (nat_lit 255)) (andB (refS (dK d) S g c)
        (andB (Nat.beq (dD d) (fD F)) (Nat.beq (fJ F) (nat_lit 0)))))) (FT g)) pc) s

@[expose] noncomputable def sEbs (FT : Nat → Nat) (S g : Nat) (s : St) : St :=
  Prod.rec (motive := fun _ => St) (fun d pc => Prod.rec (motive := fun _ => St) (fun p c =>
    (fun F => Bool.rec bad (Prod.mk (setD d (fD F)) (Prod.mk (mulF (fPiI F) p) (adv c (nat_lit 1) S)))
      (andB (Nat.beq (letAt c) (nat_lit 255)) (andB (refS (dK d) S g c)
        (andB (Nat.beq (dD d) (fDp F)) (Nat.beq (fJ F) (nat_lit 0)))))) (FT g)) pc) s

@[expose] noncomputable def sUfs (FT OT LT : Nat → Nat) (TH S g e h TAU : Nat) (s : St) : St :=
  Prod.rec (motive := fun _ => St) (fun d pc => Prod.rec (motive := fun _ => St) (fun p c =>
    (fun F => (fun O => (fun L =>
      Bool.rec bad
        (Prod.mk (setD d (fDp F)) (Prod.mk (mulF (mul12 (fPi F) (oGi' O)) (mulF (lP' L) (Nat.land TAU linMask)))
          (adv c (nat_lit 1) S)))
        (andB (Nat.beq (letAt c) (nat_lit 4)) (andB (refS (dK d) S g c)
          (andB (Nat.beq (dD d) (fD F)) (andB (Nat.blt (nat_lit 0) (fJ F)) (andB (Nat.beq (oJ O) (fJ F))
          (andB (Nat.blt e (nat_lit 512)) (andB (Nat.beq TAU (mulF (oG O) p))
            (inT TH (lamT L) h TAU)))))))))
      (LT e)) (OT (Nat.sub (fJ F) (nat_lit 1)))) (FT g)) pc) s

@[expose] noncomputable def sUbs (FT OT LT : Nat → Nat) (TH S g e h RHO : Nat) (s : St) : St :=
  Prod.rec (motive := fun _ => St) (fun d pc => Prod.rec (motive := fun _ => St) (fun p c =>
    (fun F => (fun O => (fun L =>
      Bool.rec bad
        (Prod.mk (setD d (fD F)) (Prod.mk (mulF (oGi' O) (mulF (lP' L) (Nat.land RHO linMask)))
          (adv c (nat_lit 1) S)))
        (andB (Nat.beq (letAt c) (nat_lit 4)) (andB (refS (dK d) S g c)
          (andB (Nat.beq (dD d) (fDp F)) (andB (Nat.blt (nat_lit 0) (fJ F)) (andB (Nat.beq (oJ O) (fJ F))
          (andB (Nat.blt e (nat_lit 512)) (andB (Nat.beq RHO (mulF (mul12 (oG O) (fPiI F)) p))
            (inT TH (lamT L) h RHO)))))))))
      (LT e)) (OT (Nat.sub (fJ F) (nat_lit 1)))) (FT g)) pc) s

@[expose] noncomputable def wEndJ (s : St) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun d pc => Prod.rec (motive := fun _ => Nat) (fun p c =>
    Bool.rec (motive := fun _ => Nat) FAIL (mkC (Nat.succ (dK d)) (dNd d))
      (andB (Nat.beq (dD d) (dD0 d)) (andB (Nat.beq p (dP0 d)) (Nat.beq c (nat_lit 509))))) pc) s

@[expose] noncomputable def stSm (FT HT WT : Nat → Nat) (ND NOM a b D0 w st0 : Nat) : St4 :=
  strictT st0 (fun st => Bool.rec (motive := fun _ => St4) bad4
    (strictT (mulF (hInv (HT a)) (hMat (HT b))) (fun P0 =>
      strictT (WT w) (fun W =>
        Prod.mk (mkD D0 (cIdx st) (cNd st) P0) (Prod.mk P0 (Prod.mk ident12 (wInit (wW W) (wN W)))))))
    (andB (hdrIn HT a b) (andB (Nat.blt D0 ND) (recOKm (FT (cIdx st)) (cIdx st) ND NOM))))

@[expose] noncomputable def stTr (TW : Nat → Nat) (NF st0 : Nat) : St4 :=
  strictT st0 (fun st => strictT (TW (cIdx st)) (fun W =>
    Prod.mk (mkD (nat_lit 0) NF (cIdx st) ident12)
      (Prod.mk ident12 (Prod.mk ident12 (Nat.lor (wInit (wW W) (wN W)) (nat_lit 1))))))

@[expose] noncomputable def sgN (G : Nat) : Nat := Nat.land G (nat_lit 255)
@[expose] noncomputable def sgM (G : Nat) : Nat := Nat.land (Nat.shiftRight G (nat_lit 8)) mask144
@[expose] noncomputable def sgW (G : Nat) : Nat := Nat.shiftRight G (nat_lit 152)

@[expose] noncomputable def segOK (LET G : Nat) : Bool :=
  andB (Nat.blt (nat_lit 0) (sgN G)) (andB (wFits (sgW G) (sgN G))
    (andB (letsBelow (sgW G) (sgN G) (nat_lit 4)) (chkEval LET (sgW G) (sgN G) (sgM G))))

@[expose] noncomputable def segAt (SG : Nat → Nat) (LET e : Nat) : Bool := segOK LET (SG e)

@[expose] noncomputable def mNs (SG : Nat → Nat) (e : Nat) (s : St4) : St4 :=
  Prod.rec (motive := fun _ => St4) (fun d r => Prod.rec (motive := fun _ => St4) (fun p r2 =>
    Prod.rec (motive := fun _ => St4) (fun n c =>
      (fun G => Bool.rec bad4 (Prod.mk d (Prod.mk (mul12 p (sgM G)) (Prod.mk n (adv c (sgN G) (nat_lit 0)))))
        (andB (Nat.blt (nat_lit 0) (sgN G)) (Nat.beq (letsAt c (sgN G)) (sgW G)))) (SG e)) r2) r) s

@[expose] noncomputable def mEfs (FT : Nat → Nat) (S g : Nat) (s : St4) : St4 :=
  Prod.rec (motive := fun _ => St4) (fun d r => Prod.rec (motive := fun _ => St4) (fun p r2 =>
    Prod.rec (motive := fun _ => St4) (fun n c =>
      (fun F => Bool.rec bad4 (Prod.mk (setD d (fDp F)) (Prod.mk (mulF (fPi F) p) (Prod.mk (mulF n (fNs F)) (adv c (nat_lit 1) S))))
        (andB (Nat.beq (letAt c) (nat_lit 255)) (andB (refS (dK d) S g c)
          (andB (Nat.beq (dD d) (fD F)) (Nat.beq (fJ F) (nat_lit 0)))))) (FT g)) r2) r) s

@[expose] noncomputable def mEbs (FT : Nat → Nat) (S g : Nat) (s : St4) : St4 :=
  Prod.rec (motive := fun _ => St4) (fun d r => Prod.rec (motive := fun _ => St4) (fun p r2 =>
    Prod.rec (motive := fun _ => St4) (fun n c =>
      (fun F => Bool.rec bad4 (Prod.mk (setD d (fD F)) (Prod.mk (mulF (fPiI F) p) (Prod.mk (mulF n (fNIs F)) (adv c (nat_lit 1) S))))
        (andB (Nat.beq (letAt c) (nat_lit 255)) (andB (refS (dK d) S g c)
          (andB (Nat.beq (dD d) (fDp F)) (Nat.beq (fJ F) (nat_lit 0)))))) (FT g)) r2) r) s

@[expose] noncomputable def mTfs (FT OT : Nat → Nat) (TH S g h PP : Nat) (s : St4) : St4 :=
  Prod.rec (motive := fun _ => St4) (fun d r => Prod.rec (motive := fun _ => St4) (fun p r2 =>
    Prod.rec (motive := fun _ => St4) (fun n c =>
      (fun F => (fun O =>
        Bool.rec bad4 (Prod.mk (setD d (fDp F)) (Prod.mk (mulF (fPi F) PP) (Prod.mk (mulF n (fNs F)) (adv c (nat_lit 1) S))))
          (andB (Nat.beq (letAt c) (nat_lit 4)) (andB (refS (dK d) S g c)
            (andB (Nat.beq (dD d) (fD F)) (andB (Nat.blt (nat_lit 0) (fJ F)) (andB (Nat.beq (oJ O) (fJ F))
            (andB (Nat.beq p PP) (chkPtF (oP O) PP TH h))))))))
        (OT (Nat.sub (fJ F) (nat_lit 1)))) (FT g)) r2) r) s

@[expose] noncomputable def mTbs (FT OT : Nat → Nat) (TH S g h PP RR : Nat) (s : St4) : St4 :=
  Prod.rec (motive := fun _ => St4) (fun d r => Prod.rec (motive := fun _ => St4) (fun p r2 =>
    Prod.rec (motive := fun _ => St4) (fun n c =>
      (fun F => (fun O =>
        Bool.rec bad4 (Prod.mk (setD d (fD F)) (Prod.mk RR (Prod.mk (mulF n (fNIs F)) (adv c (nat_lit 1) S))))
          (andB (Nat.beq (letAt c) (nat_lit 4)) (andB (refS (dK d) S g c)
            (andB (Nat.beq (dD d) (fDp F)) (andB (Nat.blt (nat_lit 0) (fJ F)) (andB (Nat.beq (oJ O) (fJ F))
            (andB (Nat.beq p PP) (andB (Nat.beq RR (mulF (fPiI F) PP)) (chkPtF (oP O) RR TH h)))))))))
        (OT (Nat.sub (fJ F) (nat_lit 1)))) (FT g)) r2) r) s

@[expose] noncomputable def mEndJ (s : St4) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun d r => Prod.rec (motive := fun _ => Nat) (fun p r2 =>
    Prod.rec (motive := fun _ => Nat) (fun n c =>
      Bool.rec (motive := fun _ => Nat) FAIL (mkC (Nat.succ (dK d)) (dNd d))
        (andB (Nat.beq (dD d) (dD0 d)) (andB (Nat.beq p (dP0 d)) (andB (Nat.beq n ident12) (Nat.beq c (nat_lit 509))))))
      r2) r) s

@[expose] noncomputable def trEnd (s : St4) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun d r => Prod.rec (motive := fun _ => Nat) (fun p r2 =>
    Prod.rec (motive := fun _ => Nat) (fun n c =>
      Bool.rec (motive := fun _ => Nat) FAIL (Nat.succ (dNd d))
        (andB (Nat.beq (dD d) (nat_lit 0)) (andB (Nat.beq (mul12 n p) ident12) (Nat.beq c (nat_lit 509)))))
      r2) r) s

@[expose] noncomputable def cov0 (FT : Nat → Nat) (ND g : Nat) : Bool :=
  letB (FT g) (fun F => andB (Nat.beq (fD F) (nat_lit 0)) (andB (Nat.blt (nat_lit 0) (fJ F)) (Nat.blt (fDp F) ND)))

@[expose] noncomputable def forStep (FT PT OT : Nat → Nat) (ND NOM D e BM : Nat) : Nat :=
  strictN (Nat.land (Nat.shiftRight e (nat_lit 1)) (nat_lit 32767)) (fun i => Bool.rec (motive := fun _ => Nat) (Nat.lor BM (Nat.shiftLeft (nat_lit 1) NOM))
    (Nat.lor BM (Nat.shiftLeft (nat_lit 1) i))
    (andB (Nat.blt i NOM) (andB (Nat.beq (Nat.land BM (Nat.shiftLeft (nat_lit 1) i)) (nat_lit 0))
      (Bool.rec (motive := fun _ => Bool)
        ((fun r => letB (FT (Nat.shiftRight r (nat_lit 1))) (fun F => andB (Nat.beq (oJ (OT i)) (Nat.succ i)) (
          Bool.rec (motive := fun _ => Bool)
            (andB (Nat.beq (fD F) D) (andB (Nat.beq (fJ F) (Nat.succ i)) (Nat.blt (fDp F) ND)))
            (andB (Nat.beq (fDp F) D) (andB (Nat.blt (nat_lit 0) (fJ F)) (andB (Nat.blt (fD F) ND)
              (chkPtF (PT i) (fPi F) (PT (Nat.sub (fJ F) (nat_lit 1))) (Nat.land (Nat.shiftRight e (nat_lit 32)) (nat_lit 7))))))
            (Nat.beq (Nat.land r (nat_lit 1)) (nat_lit 1)))))
          (Nat.land (Nat.shiftRight e (nat_lit 16)) (nat_lit 65535)))
        ((fun p => letB (FT (Nat.land (Nat.shiftRight e (nat_lit 32)) (nat_lit 65535))) (fun F =>
          andB (Nat.beq (fD F) D) (andB (Nat.beq (fDp F) D) (andB (Nat.beq (fJ F) (nat_lit 0))
          (andB (Nat.blt (nat_lit 0) (Nat.land BM (Nat.shiftLeft (nat_lit 1) p)))
            (chkPtF (PT p) (fPi F) (PT i) (Nat.land (Nat.shiftRight e (nat_lit 48)) (nat_lit 7))))))))
          (Nat.land (Nat.shiftRight e (nat_lit 16)) (nat_lit 32767)))
        (Nat.beq (Nat.land e (nat_lit 1)) (nat_lit 1))))))

@[expose] noncomputable def forRun (FT PT OT : Nat → Nat) (ND NOM D C m BM : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ BM => BM)
    (fun _ ih C BM => strictN C (fun C' => strictN (Nat.land C' (nat_lit 18446744073709551615)) (fun e =>
      strictN (forStep FT PT OT ND NOM D e BM) (fun B => ih (Nat.shiftRight C' (nat_lit 64)) B)))) m C BM

@[expose] noncomputable def eEnt (ET : Nat → Nat) (e : Nat) : Nat := ET e
@[expose] noncomputable def eM (E : Nat) : Nat := Nat.land E mask144
@[expose] noncomputable def eK (E : Nat) : Nat := Nat.land (Nat.shiftRight E (nat_lit 144)) (nat_lit 15)
@[expose] noncomputable def eA (E : Nat) : Nat := Nat.land (Nat.shiftRight E (nat_lit 148)) (nat_lit 65535)
@[expose] noncomputable def eB (E : Nat) : Nat := Nat.shiftRight E (nat_lit 164)

@[expose] noncomputable def gmHas (GM b : Nat) : Bool := Nat.blt (nat_lit 0) (Nat.land GM (Nat.shiftLeft (nat_lit 1) b))

@[expose] noncomputable def etOK (FT ET : Nat → Nat) (LET W0 TR Dc GM e : Nat) : Bool :=
  letB (eEnt ET e) (fun E =>
    Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool)
      (andB (Nat.beq (eK E) (nat_lit 5)) (andB (Nat.blt (eA E) e)
        (Nat.beq (mulF (eM E) (eM (eEnt ET (eA E)))) ident12)))
      (andB (Nat.blt (eA E) e) (andB (Nat.blt (eB E) e)
        (Nat.beq (eM E) (mulF (eM (eEnt ET (eA E))) (eM (eEnt ET (eB E)))))))
      (Nat.beq (eK E) (nat_lit 4)))
      (andB (gmHas GM (nat_lit 10)) (Nat.beq (eM E) TR))
      (Nat.beq (eK E) (nat_lit 3)))
      (andB (gmHas GM (nat_lit 9)) (Nat.beq (eM E) W0))
      (Nat.beq (eK E) (nat_lit 2)))
      (andB (gmHas GM (nat_lit 8)) (letB (FT (eA E)) (fun F =>
        andB (Nat.beq (fD F) Dc) (andB (Nat.beq (fDp F) Dc) (andB (Nat.beq (fJ F) (nat_lit 0))
          (Nat.beq (eM E) (fPi F)))))))
      (Nat.beq (eK E) (nat_lit 1)))
    (andB (Nat.blt (eA E) (nat_lit 7)) (andB (gmHas GM (eA E))
      (andB (Nat.blt (nat_lit 0) (eM E)) (Nat.beq (eM E) (letMat LET (eA E))))))
    (Nat.beq (eK E) (nat_lit 0)))

@[expose] noncomputable def lvN (R : Nat) : Nat := Nat.land R (nat_lit 65535)
@[expose] noncomputable def lvNg (R : Nat) : Nat := Nat.land (Nat.shiftRight R (nat_lit 16)) (nat_lit 255)
@[expose] noncomputable def lvGen (R k : Nat) : Nat :=
  Nat.land (Nat.shiftRight R (Nat.add (nat_lit 24) (Nat.mul (nat_lit 16) k))) (nat_lit 65535)
@[expose] noncomputable def lvL (R : Nat) : Nat :=
  Nat.land (Nat.shiftRight R (Nat.add (nat_lit 24) (Nat.mul (nat_lit 16) (lvNg R))))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 12) (lvN R))) (nat_lit 1))
@[expose] noncomputable def lvPG (R : Nat) : Nat :=
  Nat.shiftRight R (Nat.add (nat_lit 24) (Nat.add (Nat.mul (nat_lit 16) (lvNg R)) (Nat.mul (nat_lit 12) (lvN R))))

@[expose] noncomputable def lvG (ET : Nat → Nat) (ne R : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k acc => Nat.lor acc
    (Nat.shiftLeft (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (eM (eEnt ET (lvGen R k))) (Nat.blt (lvGen R k) ne))
      (Nat.mul (nat_lit 144) k))) (lvNg R)

@[expose] noncomputable def gensBelow (R ne : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k acc => andB acc (Nat.blt (lvGen R k) ne)) (lvNg R)

@[expose] noncomputable def treeOKs (L PG G ng n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k acc => andB acc (orB (Nat.beq k (nat_lit 0))
    (andB (Nat.blt (lpar PG k) k) (andB (Nat.blt (lgen PG k) ng) (andB (Nat.blt (nat_lit 0) (lv L k))
      (Nat.beq (strictN (lv L (lpar PG k)) (fun v => strictN (gmat G (lgen PG k)) (fun M => vecmul v M))) (lv L k))))))) n

@[expose] noncomputable def fixAll (G ng B nb : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k acc => andB acc
    (Nat.rec (motive := fun _ => Bool) true (fun i acc2 => andB acc2
      (chkFix (lv B i) (gmat G k))) nb)) ng

@[expose] noncomputable def chLevel (ET : Nat → Nat) (ne R st : Nat) : Nat :=
  strictN (lvG ET ne R) (fun G => strictN (lvL R) (fun L => strictN (lvPG R) (fun PG =>
  strictN (lvN R) (fun n => strictN (lvNg R) (fun ng =>
  strictN (Nat.land st (nat_lit 18446744073709551615)) (fun prod =>
  strictN (Nat.land (Nat.shiftRight st (nat_lit 64)) (nat_lit 255)) (fun nb =>
  strictN (Nat.shiftRight st (nat_lit 72)) (fun B =>
    Bool.rec (motive := fun _ => Nat) (nat_lit 0)
      (Nat.lor (Nat.mul prod n) (Nat.lor (Nat.shiftLeft (Nat.succ nb) (nat_lit 64))
        (Nat.shiftLeft (Nat.lor B (Nat.shiftLeft (lv L (nat_lit 0)) (Nat.mul (nat_lit 12) nb))) (nat_lit 72))))
      (andB (Nat.blt (nat_lit 0) n) (andB (Nat.blt (nat_lit 0) (lv L (nat_lit 0)))
      (andB (Nat.blt (Nat.mul prod n) (nat_lit 18446744073709551616))
      (andB (Nat.blt nb (nat_lit 255)) (andB (gensBelow R ne)
      (andB (Nat.beq (popcount (orAll L n) (nat_lit 4096)) n)
      (andB (treeOKs L PG G ng n)
        (fixAll G ng B nb))))))))))))))))

@[expose] noncomputable def chainRun (FT ET : Nat → Nat) (LET W0 TR Dc GM ne : Nat) (lvls : List Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0)
    (Nat.land (List.rec (motive := fun _ => Nat → Nat) (fun st => st)
      (fun R _ ih st => strictN (chLevel ET ne R st) ih) lvls (nat_lit 1)) (nat_lit 18446744073709551615))
    (rngAll (nat_lit 0) ne (Nat.add (Nat.shiftRight ne (nat_lit 6)) (nat_lit 1)) (etOK FT ET LET W0 TR Dc GM))

@[expose] noncomputable def tget (T : Nat → Nat) (w lg i : Nat) : Nat :=
  strictN (Nat.shiftRight i lg) (fun b =>
    Nat.land (Nat.shiftRight (T b) (Nat.mul w (Nat.land i (Nat.sub (Nat.shiftLeft (nat_lit 1) lg) (nat_lit 1)))))
      (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1)))

@[expose] noncomputable def tgetN (T : Nat → Nat) (w lg n i : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0) (tget T w lg i) (Nat.blt i n)

end CFSG.KJ4.S

end
