module

public import CFSG.Certificates.Kernel.Orders.Cert

public section

namespace CFSG.KC.Fam

open CFSG.KC.Loop CFSG.KC.Ord

@[expose] noncomputable def regEq (RB : Nat → Nat) (nreg a b : Nat) : Bool :=
  andB (regBelow a nreg) (andB (regBelow b nreg) (Nat.beq (RB a) (RB b)))

@[expose] noncomputable def commOK (RB : Nat → Nat) (mul : Nat → Nat → Nat) (nreg a b : Nat) : Bool :=
  andB (regBelow a nreg) (andB (regBelow b nreg) (Nat.beq (mul (RB a) (RB b)) (mul (RB b) (RB a))))

@[expose] noncomputable def properOK (mul : Nat → Nat → Nat) (ONE M q : Nat) (ps : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun l _ ih => andB (notB (Nat.beq (powR mul ONE M (Nat.div q l)) ONE)) ih) ps

@[expose] noncomputable def ordExact (RB : Nat → Nat) (mul : Nat → Nat → Nat) (ONE nreg r q : Nat)
    (ps : List Nat) : Bool :=
  andB (regBelow r nreg) (andB (Nat.beq (powR mul ONE (RB r) q) ONE) (properOK mul ONE (RB r) q ps))

@[expose] noncomputable def letL (RB : Nat → Nat) (GR IR : Nat) (x : Nat × Bool) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun g s => RB (Bool.rec (motive := fun _ => Nat) (at16 IR g) (at16 GR g) s)) x

@[expose] noncomputable def wordProd (RB : Nat → Nat) (mul : Nat → Nat → Nat) (ONE GR IR : Nat)
    (l : List (Nat × Bool)) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun x _ ih acc => strictN ((fun m => Bool.rec (motive := fun _ => Nat) (mul acc m) m (Nat.beq acc ONE))
      (letL RB GR IR x)) ih) l

@[expose] noncomputable def relOKL (RB : Nat → Nat) (mul : Nat → Nat → Nat) (rels : List (List (Nat × Bool)))
    (ONE GR IR r : Nat) : Bool :=
  andB (Nat.blt r (lenL rels)) (Nat.beq (wordProd RB mul ONE GR IR (nthRel rels r) ONE) ONE)

@[expose] noncomputable def invPairs (RB : Nat → Nat) (mul : Nat → Nat → Nat) (ONE nreg GR IR L : Nat) : Bool :=
  andB (regsIn GR L nreg) (andB (regsIn IR L nreg) (Nat.rec (motive := fun _ => Bool) true
    (fun g ih => andB ih (Nat.beq (mul (RB (at16 GR g)) (RB (at16 IR g))) ONE)) L))

@[expose] noncomputable def fixedOK (RB : Nat → Nat) (vm : Nat → Nat → Nat) (vldV : Nat → Bool) (nreg v r : Nat) :
    Bool :=
  andB (regBelow r nreg) (andB (vldV v) (Nat.beq (vm v (RB r)) v))

@[expose] noncomputable def subOne (p w T L H ONE X : Nat) : Nat :=
  redP w L H p T (Nat.add X (Nat.mul (Nat.sub p (nat_lit 1)) ONE))

@[expose] noncomputable def kerLineOK (p w T L H CM ONE : Nat) (mul : Nat → Nat → Nat) (vld vldV : Nat → Bool)
    (X1 X2 X3 Y1 Y2 Y3 C0 v : Nat) : Bool :=
  andB (vld Y1) (andB (vld Y2) (andB (vld Y3) (andB (vld C0) (andB (Nat.beq (Nat.land C0 CM) C0) (andB (vldV v)
    (Nat.beq (redP w L H p T (Nat.add (Nat.add (Nat.add
        (mul (subOne p w T L H ONE X1) Y1) (mul (subOne p w T L H ONE X2) Y2))
        (mul (subOne p w T L H ONE X3) Y3)) (Nat.mul C0 v))) ONE))))))

@[expose] noncomputable def bfsStep (V : Nat → Nat) (vm : Nat → Nat → Nat) (G0 G1 mx S ev : Nat) : Nat :=
  (fun c e => (fun i img => nIf(andB (Nat.blt (nat_lit 0) S) (andB (Nat.blt i c) (Nat.blt c mx)),
        nIf(Nat.beq ev (nat_lit 1),
          nIf(Nat.beq (V c) img, Nat.add (Nat.succ c) (Nat.shiftLeft (Nat.succ e) (nat_lit 8)), nat_lit 0),
          nIf(andB (Nat.beq (Nat.land ev (nat_lit 1)) (nat_lit 0)) (andB (Nat.blt (Nat.shiftRight ev (nat_lit 1)) c)
              (Nat.beq (V (Nat.shiftRight ev (nat_lit 1))) img)),
            Nat.add c (Nat.shiftLeft (Nat.succ e) (nat_lit 8)), nat_lit 0)),
        nat_lit 0))
      (Nat.shiftRight e (nat_lit 1))
      (vm (V (Nat.shiftRight e (nat_lit 1))) (nIf(Nat.beq (Nat.land e (nat_lit 1)) (nat_lit 0), G0, G1))))
    (Nat.land S (nat_lit 255)) (Nat.shiftRight S (nat_lit 8))

@[expose] noncomputable def bfsRun (V : Nat → Nat) (vm : Nat → Nat → Nat) (G0 G1 mx : Nat) (Cs : List Nat) :
    Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => strictN (bfsStep V vm G0 G1 mx S (Nat.land J (nat_lit 255))) (ih2 (Nat.shiftRight J (nat_lit 8))))
        (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S) ih) Cs

@[expose] noncomputable def wordStep (WD : Nat → Nat) (S ev : Nat) : Nat :=
  (fun c e => nIf(Nat.blt (nat_lit 0) S,
      nIf(Nat.beq ev (nat_lit 1),
        nIf(Nat.beq (WD c) (Nat.add (Nat.succ (Nat.land (WD (Nat.shiftRight e (nat_lit 1))) (nat_lit 255)))
              (Nat.shiftLeft (Nat.add (Nat.succ (Nat.land e (nat_lit 1)))
                (Nat.shiftLeft (Nat.shiftRight (WD (Nat.shiftRight e (nat_lit 1))) (nat_lit 8)) (nat_lit 2))) (nat_lit 8))),
          Nat.add (Nat.succ c) (Nat.shiftLeft (Nat.succ e) (nat_lit 8)), nat_lit 0),
        Nat.add c (Nat.shiftLeft (Nat.succ e) (nat_lit 8))),
      nat_lit 0))
    (Nat.land S (nat_lit 255)) (Nat.shiftRight S (nat_lit 8))

@[expose] noncomputable def bfsWords (WD : Nat → Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => strictN (wordStep WD S (Nat.land J (nat_lit 255))) (ih2 (Nat.shiftRight J (nat_lit 8))))
        (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S) ih) Cs

@[expose] noncomputable def rowsMat (V : Nat → Nat) (vldV : Nat → Bool) (S d : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => nIf(vldV (V k), Nat.lor acc (Nat.shiftLeft (V k) (Nat.mul S k)), nat_lit 0)) d

@[expose] noncomputable def rowsBasis (V : Nat → Nat) (mul : Nat → Nat → Nat) (vld vldV : Nat → Bool)
    (S d ONE Ri : Nat) : Bool :=
  andB (allBelow d (Nat.add (Nat.shiftRight d (nat_lit 6)) (nat_lit 1)) (fun k => vldV (V k)))
    (andB (vld Ri) (Nat.beq (mul (rowsMat V vldV S d) Ri) ONE))

@[expose] noncomputable def dualOK (RB : Nat → Nat) (vm : Nat → Nat → Nat) (vldV : Nat → Bool) (nreg UL n k w : Nat) :
    Bool :=
  andB (vldV w) (andB (regsIn UL n nreg) (Nat.rec (motive := fun _ => Bool) true
    (fun j ih => andB ih (Bool.rec (motive := fun _ => Bool)
      (Nat.beq (vm w (RB (at16 UL j))) w) (notB (Nat.beq (vm w (RB (at16 UL j))) w)) (Nat.beq j k))) n))

@[expose] noncomputable def fld64 (x k : Nat) : Nat := bitsN x (Nat.mul (nat_lit 64) k) (nat_lit 64)

@[expose] noncomputable def subSize (sizes mask n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 1)
    (fun k acc => Nat.add acc (Nat.mul (bitsN mask k (nat_lit 1)) (fld64 sizes k))) n

@[expose] noncomputable def primSub (sizes n N : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun mask acc => andB acc (orB (orB (Nat.beq mask (nat_lit 0))
        (Nat.beq mask (Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1))))
      (notB (Nat.beq (Nat.mod N (subSize sizes mask n)) (nat_lit 0)))))
    (Nat.shiftLeft (nat_lit 1) n)

@[expose] noncomputable def sumIs (sizes n N : Nat) : Bool :=
  Nat.beq (subSize sizes (Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1)) n) N

@[expose] noncomputable def coprime (a b : Nat) : Bool := Nat.beq (Nat.gcd a b) (nat_lit 1)

@[expose] noncomputable def conjOK (mul : Nat → Nat → Nat) (vld : Nat → Bool) (ONE C Ci X Y : Nat) : Bool :=
  andB (vld C) (andB (vld Ci) (andB (Nat.beq (mul C Ci) ONE) (Nat.beq (mul X C) (mul C Y))))

end CFSG.KC.Fam

end
