module

public import CFSG.Certificates.Kernel.Common.Lce

public section

namespace CFSG.KC

@[expose] noncomputable def pmul (a b : Nat) : Nat :=
  Nat.lor (Nat.land (Nat.shiftRight b (Nat.shiftLeft (Nat.land a (nat_lit 15)) (nat_lit 2))) (nat_lit 15)) <|
  Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight b (Nat.shiftLeft (Nat.land (Nat.shiftRight a (nat_lit 4)) (nat_lit 15)) (nat_lit 2))) (nat_lit 15)) (nat_lit 4)) <|
  Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight b (Nat.shiftLeft (Nat.land (Nat.shiftRight a (nat_lit 8)) (nat_lit 15)) (nat_lit 2))) (nat_lit 15)) (nat_lit 8)) <|
  Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight b (Nat.shiftLeft (Nat.land (Nat.shiftRight a (nat_lit 12)) (nat_lit 15)) (nat_lit 2))) (nat_lit 15)) (nat_lit 12)) <|
  Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight b (Nat.shiftLeft (Nat.land (Nat.shiftRight a (nat_lit 16)) (nat_lit 15)) (nat_lit 2))) (nat_lit 15)) (nat_lit 16)) <|
  Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight b (Nat.shiftLeft (Nat.land (Nat.shiftRight a (nat_lit 20)) (nat_lit 15)) (nat_lit 2))) (nat_lit 15)) (nat_lit 20)) <|
  Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight b (Nat.shiftLeft (Nat.land (Nat.shiftRight a (nat_lit 24)) (nat_lit 15)) (nat_lit 2))) (nat_lit 15)) (nat_lit 24)) <|
  Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight b (Nat.shiftLeft (Nat.land (Nat.shiftRight a (nat_lit 28)) (nat_lit 15)) (nat_lit 2))) (nat_lit 15)) (nat_lit 28)) <|
  Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight b (Nat.shiftLeft (Nat.land (Nat.shiftRight a (nat_lit 32)) (nat_lit 15)) (nat_lit 2))) (nat_lit 15)) (nat_lit 32)) <|
  Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight b (Nat.shiftLeft (Nat.land (Nat.shiftRight a (nat_lit 36)) (nat_lit 15)) (nat_lit 2))) (nat_lit 15)) (nat_lit 36)) <|
  Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight b (Nat.shiftLeft (Nat.land (Nat.shiftRight a (nat_lit 40)) (nat_lit 15)) (nat_lit 2))) (nat_lit 15)) (nat_lit 40)) <|
  Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight b (Nat.shiftLeft (Nat.land (Nat.shiftRight a (nat_lit 44)) (nat_lit 15)) (nat_lit 2))) (nat_lit 15)) (nat_lit 44)) <|
  Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight b (Nat.shiftLeft (Nat.land (Nat.shiftRight a (nat_lit 48)) (nat_lit 15)) (nat_lit 2))) (nat_lit 15)) (nat_lit 48)) <|
  Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight b (Nat.shiftLeft (Nat.land (Nat.shiftRight a (nat_lit 52)) (nat_lit 15)) (nat_lit 2))) (nat_lit 15)) (nat_lit 52)) <|
  Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight b (Nat.shiftLeft (Nat.land (Nat.shiftRight a (nat_lit 56)) (nat_lit 15)) (nat_lit 2))) (nat_lit 15)) (nat_lit 56))
    (Nat.shiftLeft (Nat.land (Nat.shiftRight b (Nat.shiftLeft (Nat.shiftRight a (nat_lit 60)) (nat_lit 2))) (nat_lit 15)) (nat_lit 60))

@[expose] noncomputable def pinv (a : Nat) : Nat :=
  Nat.lor (Nat.shiftLeft (nat_lit 0) (Nat.shiftLeft (Nat.land a (nat_lit 15)) (nat_lit 2))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.shiftLeft (Nat.land (Nat.shiftRight a (nat_lit 4)) (nat_lit 15)) (nat_lit 2))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 2) (Nat.shiftLeft (Nat.land (Nat.shiftRight a (nat_lit 8)) (nat_lit 15)) (nat_lit 2))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 3) (Nat.shiftLeft (Nat.land (Nat.shiftRight a (nat_lit 12)) (nat_lit 15)) (nat_lit 2))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 4) (Nat.shiftLeft (Nat.land (Nat.shiftRight a (nat_lit 16)) (nat_lit 15)) (nat_lit 2))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 5) (Nat.shiftLeft (Nat.land (Nat.shiftRight a (nat_lit 20)) (nat_lit 15)) (nat_lit 2))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 6) (Nat.shiftLeft (Nat.land (Nat.shiftRight a (nat_lit 24)) (nat_lit 15)) (nat_lit 2))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 7) (Nat.shiftLeft (Nat.land (Nat.shiftRight a (nat_lit 28)) (nat_lit 15)) (nat_lit 2))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 8) (Nat.shiftLeft (Nat.land (Nat.shiftRight a (nat_lit 32)) (nat_lit 15)) (nat_lit 2))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 9) (Nat.shiftLeft (Nat.land (Nat.shiftRight a (nat_lit 36)) (nat_lit 15)) (nat_lit 2))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 10) (Nat.shiftLeft (Nat.land (Nat.shiftRight a (nat_lit 40)) (nat_lit 15)) (nat_lit 2))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 11) (Nat.shiftLeft (Nat.land (Nat.shiftRight a (nat_lit 44)) (nat_lit 15)) (nat_lit 2))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 12) (Nat.shiftLeft (Nat.land (Nat.shiftRight a (nat_lit 48)) (nat_lit 15)) (nat_lit 2))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 13) (Nat.shiftLeft (Nat.land (Nat.shiftRight a (nat_lit 52)) (nat_lit 15)) (nat_lit 2))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 14) (Nat.shiftLeft (Nat.land (Nat.shiftRight a (nat_lit 56)) (nat_lit 15)) (nat_lit 2)))
    (Nat.shiftLeft (nat_lit 15) (Nat.shiftLeft (Nat.shiftRight a (nat_lit 60)) (nat_lit 2)))

@[expose] noncomputable def isPerm (a : Nat) : Bool :=
  andB (Nat.blt a (nat_lit 18446744073709551616)) <| Nat.beq (nat_lit 65535) <|
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.land a (nat_lit 15))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.land (Nat.shiftRight a (nat_lit 4)) (nat_lit 15))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.land (Nat.shiftRight a (nat_lit 8)) (nat_lit 15))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.land (Nat.shiftRight a (nat_lit 12)) (nat_lit 15))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.land (Nat.shiftRight a (nat_lit 16)) (nat_lit 15))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.land (Nat.shiftRight a (nat_lit 20)) (nat_lit 15))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.land (Nat.shiftRight a (nat_lit 24)) (nat_lit 15))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.land (Nat.shiftRight a (nat_lit 28)) (nat_lit 15))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.land (Nat.shiftRight a (nat_lit 32)) (nat_lit 15))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.land (Nat.shiftRight a (nat_lit 36)) (nat_lit 15))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.land (Nat.shiftRight a (nat_lit 40)) (nat_lit 15))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.land (Nat.shiftRight a (nat_lit 44)) (nat_lit 15))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.land (Nat.shiftRight a (nat_lit 48)) (nat_lit 15))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.land (Nat.shiftRight a (nat_lit 52)) (nat_lit 15))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.land (Nat.shiftRight a (nat_lit 56)) (nat_lit 15)))
    (Nat.shiftLeft (nat_lit 1) (Nat.shiftRight a (nat_lit 60)))

@[expose] noncomputable def imgMasks (P PB : Nat) : Nat :=
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (Nat.land PB (nat_lit 15)) (nat_lit 4)) (Nat.land P (nat_lit 15)))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (Nat.land (Nat.shiftRight PB (nat_lit 4)) (nat_lit 15)) (nat_lit 4)) (Nat.land (Nat.shiftRight P (nat_lit 4)) (nat_lit 15)))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (Nat.land (Nat.shiftRight PB (nat_lit 8)) (nat_lit 15)) (nat_lit 4)) (Nat.land (Nat.shiftRight P (nat_lit 8)) (nat_lit 15)))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (Nat.land (Nat.shiftRight PB (nat_lit 12)) (nat_lit 15)) (nat_lit 4)) (Nat.land (Nat.shiftRight P (nat_lit 12)) (nat_lit 15)))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (Nat.land (Nat.shiftRight PB (nat_lit 16)) (nat_lit 15)) (nat_lit 4)) (Nat.land (Nat.shiftRight P (nat_lit 16)) (nat_lit 15)))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (Nat.land (Nat.shiftRight PB (nat_lit 20)) (nat_lit 15)) (nat_lit 4)) (Nat.land (Nat.shiftRight P (nat_lit 20)) (nat_lit 15)))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (Nat.land (Nat.shiftRight PB (nat_lit 24)) (nat_lit 15)) (nat_lit 4)) (Nat.land (Nat.shiftRight P (nat_lit 24)) (nat_lit 15)))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (Nat.land (Nat.shiftRight PB (nat_lit 28)) (nat_lit 15)) (nat_lit 4)) (Nat.land (Nat.shiftRight P (nat_lit 28)) (nat_lit 15)))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (Nat.land (Nat.shiftRight PB (nat_lit 32)) (nat_lit 15)) (nat_lit 4)) (Nat.land (Nat.shiftRight P (nat_lit 32)) (nat_lit 15)))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (Nat.land (Nat.shiftRight PB (nat_lit 36)) (nat_lit 15)) (nat_lit 4)) (Nat.land (Nat.shiftRight P (nat_lit 36)) (nat_lit 15)))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (Nat.land (Nat.shiftRight PB (nat_lit 40)) (nat_lit 15)) (nat_lit 4)) (Nat.land (Nat.shiftRight P (nat_lit 40)) (nat_lit 15)))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (Nat.land (Nat.shiftRight PB (nat_lit 44)) (nat_lit 15)) (nat_lit 4)) (Nat.land (Nat.shiftRight P (nat_lit 44)) (nat_lit 15)))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (Nat.land (Nat.shiftRight PB (nat_lit 48)) (nat_lit 15)) (nat_lit 4)) (Nat.land (Nat.shiftRight P (nat_lit 48)) (nat_lit 15)))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (Nat.land (Nat.shiftRight PB (nat_lit 52)) (nat_lit 15)) (nat_lit 4)) (Nat.land (Nat.shiftRight P (nat_lit 52)) (nat_lit 15)))) <|
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (Nat.land (Nat.shiftRight PB (nat_lit 56)) (nat_lit 15)) (nat_lit 4)) (Nat.land (Nat.shiftRight P (nat_lit 56)) (nat_lit 15))))
    (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (Nat.land (Nat.shiftRight PB (nat_lit 60)) (nat_lit 15)) (nat_lit 4)) (Nat.shiftRight P (nat_lit 60))))

@[expose] noncomputable def fld16 (x l : Nat) : Nat := Nat.land (Nat.shiftRight x (Nat.shiftLeft l (nat_lit 4))) (nat_lit 65535)

@[expose] noncomputable def allIn (NB BB M : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun l acc => andB acc (Nat.blt (nat_lit 0) (Nat.land BB (Nat.shiftLeft (nat_lit 1) (fld16 M (Nat.succ l)))))) NB

@[expose] noncomputable def memb (NB OM m : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun l acc => orB acc (Nat.beq (fld16 OM l) m)) NB

@[expose] noncomputable def allMemb (NB OM M : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun l acc => andB acc (memb NB OM (fld16 M (Nat.succ l)))) NB

@[expose] noncomputable def pbTag (PB : Nat) : Nat := Nat.shiftRight PB (nat_lit 64)
@[expose] noncomputable def omTag (OM : Nat) : Nat := Nat.shiftRight OM (nat_lit 112)

@[expose] noncomputable def rget104 (B off : Nat) : Nat :=
  Nat.land (Nat.shiftRight B off) (nat_lit 20282409603651670423947251286015)

@[expose] noncomputable def dD (R : Nat) : Nat := Nat.land R (nat_lit 16383)
@[expose] noncomputable def dJ (R : Nat) : Nat := Nat.land (Nat.shiftRight R (nat_lit 14)) (nat_lit 2047)
@[expose] noncomputable def dDp (R : Nat) : Nat := Nat.land (Nat.shiftRight R (nat_lit 25)) (nat_lit 16383)
@[expose] noncomputable def dP (R : Nat) : Nat := Nat.shiftRight R (nat_lit 39)

@[expose] noncomputable def sD (st : Nat) : Nat := Nat.land st (nat_lit 16383)
@[expose] noncomputable def sP (st : Nat) : Nat := Nat.land (Nat.shiftRight st (nat_lit 14)) (nat_lit 18446744073709551615)
@[expose] noncomputable def sLet (st : Nat) : Nat := Nat.land (Nat.shiftRight st (nat_lit 78)) (nat_lit 255)
@[expose] noncomputable def mkSt (D P st : Nat) : Nat :=
  Nat.lor D (Nat.lor (Nat.shiftLeft P (nat_lit 14)) (Nat.shiftLeft (Nat.shiftRight st (nat_lit 86)) (nat_lit 78)))

@[expose] noncomputable def dN (c Lc st : Nat) : Nat :=
  Bool.rec (nat_lit 0) (mkSt (sD st) (pmul (sP st) Lc) st) (Nat.beq (sLet st) c)

@[expose] noncomputable def dEf (R st : Nat) : Nat :=
  Bool.rec (nat_lit 0) (mkSt (dDp R) (pmul (dP R) (sP st)) st)
    (andB (Nat.beq (sLet st) (nat_lit 255)) (andB (Nat.beq (dJ R) (nat_lit 0)) (Nat.beq (sD st) (dD R))))

@[expose] noncomputable def dEb (R st : Nat) : Nat :=
  Bool.rec (nat_lit 0) (mkSt (dD R) (pmul (pinv (dP R)) (sP st)) st)
    (andB (Nat.beq (sLet st) (nat_lit 255)) (andB (Nat.beq (dJ R) (nat_lit 0)) (Nat.beq (sD st) (dDp R))))

@[expose] noncomputable def dTf (TL NB PB BB R st : Nat) : Nat :=
  Bool.rec (nat_lit 0) (mkSt (dDp R) (pmul (dP R) (sP st)) st)
    (andB (Nat.beq (sLet st) TL) (andB (Nat.beq (dJ R) (pbTag PB)) (andB (Nat.beq (sD st) (dD R))
      (allIn NB BB (imgMasks (sP st) PB)))))

@[expose] noncomputable def dTb' (TL NB PB BB R P st : Nat) : Nat :=
  Bool.rec (nat_lit 0) (mkSt (dD R) P st)
    (andB (Nat.beq (sLet st) TL) (andB (Nat.beq (dJ R) (pbTag PB)) (andB (Nat.beq (sD st) (dDp R))
      (allIn NB BB (imgMasks P PB)))))

@[expose] noncomputable def dTb (TL NB PB BB R st : Nat) : Nat := dTb' TL NB PB BB R (pmul (pinv (dP R)) (sP st)) st

@[expose] noncomputable def dRecOK (ND NO R : Nat) : Bool :=
  andB (Nat.blt (dD R) ND) (andB (Nat.blt (dDp R) ND) (andB (Nat.ble (dJ R) NO) (isPerm (dP R))))

@[expose] noncomputable def dStart (D0 P0 W : Nat) : Nat :=
  Nat.lor D0 (Nat.lor (Nat.shiftLeft P0 (nat_lit 14)) (Nat.shiftLeft W (nat_lit 78)))

@[expose] noncomputable def dWalk (ND NO R D0 P0 st : Nat) : Bool :=
  andB (dRecOK ND NO R) (Nat.beq st (dStart D0 P0 (nat_lit 1)))

@[expose] noncomputable def dTree (ND NO ID R k : Nat) : Bool :=
  andB (dRecOK ND NO R) (andB (Nat.blt (nat_lit 0) (dJ R)) (andB (Nat.beq (dDp R) k)
    (andB (Nat.blt (dD R) k) (Nat.beq (dP R) ID))))

@[expose] noncomputable def dAx (ND NO R HIa Hb : Nat) : Bool :=
  andB (dRecOK ND NO R) (andB (Nat.beq (Nat.land R (nat_lit 549755813887)) (nat_lit 0))
    (Nat.beq (dP R) (pmul HIa Hb)))

@[expose] noncomputable def bitAt (A d : Nat) : Bool := Nat.blt (nat_lit 0) (Nat.land A (Nat.shiftLeft (nat_lit 1) d))

@[expose] noncomputable def dCovF (A R D J : Nat) : Bool :=
  andB (Nat.beq (dD R) D) (andB (Nat.beq (dJ R) J) (bitAt A (dDp R)))

@[expose] noncomputable def dCovB (NB A R D J PBw OMj : Nat) : Bool :=
  andB (Nat.beq (dDp R) D) (andB (Nat.beq (pbTag PBw) J) (andB (Nat.beq (omTag OMj) (dJ R))
    (andB (Nat.blt (nat_lit 0) (dJ R)) (andB (bitAt A (dD R)) (allMemb NB OMj (imgMasks (dP R) PBw))))))

@[expose] noncomputable def dStab (R D : Nat) : Bool :=
  andB (Nat.beq (dD R) D) (andB (Nat.beq (dJ R) (nat_lit 0)) (Nat.beq (dDp R) D))

@[expose] noncomputable def pbOK (NB ID PB OM : Nat) : Bool :=
  andB (Nat.beq (pbTag PB) (omTag OM)) (andB (allMemb NB OM (imgMasks ID PB))
    (Nat.rec (motive := fun _ => Bool) true
      (fun l acc => andB acc (Nat.blt (fld16 OM l) (fld16 OM (Nat.succ l)))) (Nat.sub NB (nat_lit 1))))

@[expose] noncomputable def gOmOK (NB PB0 g OMw : Nat) : Bool := allMemb NB OMw (imgMasks g PB0)

@[expose] noncomputable def bbOK (NB BB OM : Nat) : Bool :=
  Nat.beq BB (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun l acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (fld16 OM l))) NB)

@[expose] noncomputable def pget (B off : Nat) : Nat := Nat.land (Nat.shiftRight B off) (nat_lit 18446744073709551615)

@[expose] noncomputable def eTree (e p g : Nat) : Bool := Nat.beq (pmul p g) e

@[expose] noncomputable def eClos (e g f : Nat) : Bool := Nat.beq (pmul e g) f

end CFSG.KC

end
