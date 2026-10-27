module

public import CFSG.Certificates.Kernel.Orders.Cert

public section

namespace CFSG.KC.Fam

open CFSG.KC.Loop CFSG.KC.Ord

@[expose] noncomputable def opsOf (PM : Nat → Nat) (mul : Nat → Nat → Nat) (Bsti TL iw t : Nat) : Nat :=
  mul Bsti (PM (bitsN TL (Nat.mul iw t) iw))

@[expose] noncomputable def treeOK (PJ Top : Nat → Nat) (mul : Nat → Nat → Nat) (vld : Nat → Bool) (ONE nop PT d : Nat) : Bool :=
  andB (Nat.beq (PJ (nat_lit 0)) ONE) (Nat.rec (motive := fun _ => Bool) true
    (fun s ih => andB ih ((fun j => (fun pj tj => andB (vld (PJ j)) (andB (Nat.blt pj j) (andB (Nat.blt tj nop)
        (Nat.beq (PJ j) (mul (Top tj) (PJ pj))))))
      (bitsN PT (Nat.mul (nat_lit 16) j) (nat_lit 8)) (bitsN PT (Nat.add (Nat.mul (nat_lit 16) j) (nat_lit 8)) (nat_lit 8)))
      (Nat.succ s))) (Nat.sub d (nat_lit 1)))

@[expose] noncomputable def colsMat (PJ : Nat → Nat) (mul : Nat → Nat → Nat) (w d C0v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => Nat.lor acc (Nat.shiftLeft (mul (PJ j) C0v) (Nat.mul w j))) d

@[expose] noncomputable def relMat (PJ : Nat → Nat) (mul : Nat → Nat → Nat) (p w T L H d a Tm j : Nat) : Nat :=
  redP w L H p T (Nat.add
    (redP w L H p T (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k acc => Nat.add acc (Nat.mul (PJ k) (bitsN a (Nat.mul w k) w))) d))
    (Nat.mul (Nat.sub p (nat_lit 1)) (mul Tm (PJ j))))

@[expose] noncomputable def relOf (PJ Top RA : Nat → Nat) (mul : Nat → Nat → Nat) (p w T L H d RTJ r : Nat) : Nat :=
  relMat PJ mul p w T L H d (RA r) (Top (bitsN RTJ (Nat.mul (nat_lit 16) r) (nat_lit 8)))
    (bitsN RTJ (Nat.add (Nat.mul (nat_lit 16) r) (nat_lit 8)) (nat_lit 8))

@[expose] noncomputable def relsVanish (PJ Top RA RY : Nat → Nat) (mul : Nat → Nat → Nat) (vld vldV : Nat → Bool)
    (p w T L H d nop C0v RTJ nrec : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun r ih => andB ih (andB (Nat.blt (bitsN RTJ (Nat.mul (nat_lit 16) r) (nat_lit 8)) nop)
      (andB (Nat.blt (bitsN RTJ (Nat.add (Nat.mul (nat_lit 16) r) (nat_lit 8)) (nat_lit 8)) d)
      (andB (vldV (RA r)) (andB (vld (RY r))
        (Nat.beq (mul (relOf PJ Top RA mul p w T L H d RTJ r) C0v) (nat_lit 0))))))) nrec

@[expose] noncomputable def relSum (PJ Top RA RY : Nat → Nat) (mul : Nat → Nat → Nat) (p w T L H d RTJ nrec : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun r acc => strictN acc (fun ac => redP w L H p T (Nat.add ac (mul (RY r) (relOf PJ Top RA mul p w T L H d RTJ r))))) nrec

@[expose] noncomputable def cycCentOK (p w d T L H CM ONE : Nat) (mul : Nat → Nat → Nat) (vld vldV : Nat → Bool)
    (PJ Top RA RY : Nat → Nat) (nop PT C0v Cm Cmi ur RTJ nrec : Nat) : Bool :=
  andB (treeOK PJ Top mul vld ONE nop PT d)
    (andB (andB (vld C0v) (Nat.beq (Nat.land C0v CM) C0v))
    (andB (andB (vld Cm) (andB (vld Cmi) (andB (Nat.beq (colsMat PJ mul w d C0v) Cm) (Nat.beq (mul Cm Cmi) ONE))))
    (andB (vldV ur)
    (andB (relsVanish PJ Top RA RY mul vld vldV p w T L H d nop C0v RTJ nrec)
      (Nat.beq (redP w L H p T (Nat.add (relSum PJ Top RA RY mul p w T L H d RTJ nrec) (Nat.mul C0v ur))) ONE)))))

@[expose] noncomputable def cycTree (PJ Top : Nat → Nat) (mul : Nat → Nat → Nat) (vld : Nat → Bool) (nop PT d lo m : Nat) :
    Bool :=
  andB (Nat.blt (nat_lit 0) lo) (andB (Nat.ble (Nat.add lo m) d) (Nat.rec (motive := fun _ => Bool) true
    (fun s ih => andB ih ((fun j => (fun pj tj => andB (vld (PJ j)) (andB (Nat.blt pj j) (andB (Nat.blt tj nop)
        (Nat.beq (PJ j) (mul (Top tj) (PJ pj))))))
      (bitsN PT (Nat.mul (nat_lit 16) j) (nat_lit 8)) (bitsN PT (Nat.add (Nat.mul (nat_lit 16) j) (nat_lit 8)) (nat_lit 8)))
      (Nat.add lo s))) m))

@[expose] noncomputable def cycCols (PJ : Nat → Nat) (mul : Nat → Nat → Nat) (w d CM C0v Cm lo m : Nat) : Bool :=
  andB (Nat.ble (Nat.add lo m) d) (Nat.rec (motive := fun _ => Bool) true
    (fun s ih => andB ih ((fun j => Nat.beq (mul (PJ j) C0v) (Nat.land (Nat.shiftRight Cm (Nat.mul w j)) CM))
      (Nat.add lo s))) m)

@[expose] noncomputable def cycBasis (PJ : Nat → Nat) (mul : Nat → Nat → Nat) (vld vldV : Nat → Bool)
    (CM ONE C0v Cm Cmi ur : Nat) : Bool :=
  andB (Nat.beq (PJ (nat_lit 0)) ONE) (andB (andB (vld C0v) (Nat.beq (Nat.land C0v CM) C0v))
    (andB (vld Cm) (andB (vld Cmi) (andB (vldV ur) (Nat.beq (mul Cm Cmi) ONE)))))

@[expose] noncomputable def cycStep (PJ Top RA RY : Nat → Nat) (mul : Nat → Nat → Nat) (vld : Nat → Bool)
    (p w T L H d RTJ r Sin Sout : Nat) : Bool :=
  andB (vld Sin) (Nat.beq (redP w L H p T (Nat.add Sin (mul (RY r) (relOf PJ Top RA mul p w T L H d RTJ r)))) Sout)

@[expose] noncomputable def cycEnd (p w T L H ONE C0v ur S : Nat) : Bool :=
  Nat.beq (redP w L H p T (Nat.add S (Nat.mul C0v ur))) ONE

@[expose] noncomputable def colOf (w S d v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (bitsN v (Nat.mul w i) w) (Nat.mul S i))) d

@[expose] noncomputable def lincomb (RB : Nat → Nat) (p w T L H nreg : Nat) (Ls : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => (fun c r => nIf(andB (Nat.blt c p) (regBelow r nreg),
        redP w L H p T (Nat.add ih (Nat.mul (RB r) c)), nat_lit 0))
      (Nat.land x (nat_lit 255)) (Nat.shiftRight x (nat_lit 8))) Ls

@[expose] noncomputable def treeVecOK (V : Nat → Nat) (vm : Nat → Nat → Nat) (G0 G1 v0 PT d : Nat) : Bool :=
  andB (Nat.beq (V (nat_lit 0)) v0) (Nat.rec (motive := fun _ => Bool) true
    (fun s ih => andB ih ((fun i => (fun pi li => andB (Nat.blt pi i) (andB (Nat.ble li (nat_lit 1))
        (Nat.beq (V i) (vm (V pi) (nIf(Nat.beq li (nat_lit 0), G0, G1))))))
      (bitsN PT (Nat.mul (nat_lit 24) i) (nat_lit 16)) (bitsN PT (Nat.add (Nat.mul (nat_lit 24) i) (nat_lit 16)) (nat_lit 8)))
      (Nat.succ s))) (Nat.sub d (nat_lit 1)))

@[expose] noncomputable def rkerOK (p w T L H CM ONE : Nat) (mul : Nat → Nat → Nat) (vld vldV : Nat → Bool)
    (C Y C0v ur : Nat) : Bool :=
  andB (vld Y) (andB (vld C0v) (andB (Nat.beq (Nat.land C0v CM) C0v) (andB (vldV ur)
    (Nat.beq (redP w L H p T (Nat.add (mul Y C) (Nat.mul C0v ur))) ONE))))

@[expose] noncomputable def permRows (S d X PI : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.lor acc (Nat.shiftLeft (bitsN X (Nat.mul S (bitsN PI (Nat.mul (nat_lit 16) k) (nat_lit 16))) S) (Nat.mul S k))) d

@[expose] noncomputable def permOKd (d PI : Nat) : Bool :=
  (fun bm => Nat.beq bm (Nat.sub (Nat.shiftLeft (nat_lit 1) d) (nat_lit 1)))
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k acc => (fun x => nIf(andB (Nat.blt x d) (Nat.beq (Nat.land acc (Nat.shiftLeft (nat_lit 1) x)) (nat_lit 0)),
          Nat.lor acc (Nat.shiftLeft (nat_lit 1) x), acc))
        (bitsN PI (Nat.mul (nat_lit 16) k) (nat_lit 16))) d)

@[expose] noncomputable def invParity (d PI : Nat) : Nat :=
  Nat.mod (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.add acc (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun l acc2 => Nat.add acc2 (nIf(Nat.blt (bitsN PI (Nat.mul (nat_lit 16) (Nat.add (Nat.succ k) l)) (nat_lit 16))
          (bitsN PI (Nat.mul (nat_lit 16) k) (nat_lit 16)), nat_lit 1, nat_lit 0))) (Nat.sub (Nat.sub d k) (nat_lit 1)))) d) (nat_lit 2)

@[expose] noncomputable def diagProd (p w S d U : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 1)
    (fun i acc => Nat.mod (Nat.mul acc (bitsN U (Nat.add (Nat.mul S i) (Nat.mul w i)) w)) p) d

@[expose] noncomputable def pluOK (p w S d ONE UP DG FL : Nat) (mul : Nat → Nat → Nat) (vld : Nat → Bool)
    (X PI Lm Um det : Nat) : Bool :=
  andB (permOKd d PI) (andB (vld Lm) (andB (vld Um)
    (andB (Nat.beq (Nat.land Lm UP) (nat_lit 0)) (andB (Nat.beq (Nat.land Lm DG) ONE)
    (andB (Nat.beq (Nat.land Um (Nat.sub (Nat.sub FL UP) DG)) (nat_lit 0))
    (andB (Nat.beq (mul Lm Um) (permRows S d X PI))
      (Nat.beq (Nat.mod (Nat.mul (nIf(Nat.beq (invParity d PI) (nat_lit 0), nat_lit 1, Nat.sub p (nat_lit 1)))
        (diagProd p w S d Um)) p) det)))))))

@[expose] noncomputable def regOf (RB : Nat → Nat) (L t : Nat) : Nat := RB (at16 L t)

@[expose] noncomputable def rrefOK (w S d UT r PV : Nat) : Bool :=
  andB (Nat.beq (Nat.shiftRight UT (Nat.mul r S)) (nat_lit 0)) (Nat.rec (motive := fun _ => Bool) true
    (fun k ih => andB ih ((fun c row => andB (Nat.blt c d) (andB
        (bIf(Nat.beq k (nat_lit 0), true, Nat.blt (bitsN PV (Nat.mul (nat_lit 16) (Nat.sub k (nat_lit 1))) (nat_lit 16)) c))
        (andB (Nat.beq (bitsN row (Nat.mul w c) w) (nat_lit 1))
        (andB (Nat.beq (Nat.land row (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul w c)) (nat_lit 1))) (nat_lit 0))
          (Nat.rec (motive := fun _ => Bool) true (fun l ih2 => andB ih2
            (bIf(Nat.beq l k, true, Nat.beq (bitsN (bitsN UT (Nat.mul S l) S) (Nat.mul w c) w) (nat_lit 0)))) r)))))
      (bitsN PV (Nat.mul (nat_lit 16) k) (nat_lit 16)) (bitsN UT (Nat.mul S k) S))) r)

@[expose] noncomputable def colsBelow (w S d M k : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => andB ih (Nat.beq (Nat.shiftRight (bitsN M (Nat.mul S i) S) (Nat.mul w k)) (nat_lit 0))) d

end CFSG.KC.Fam

end
