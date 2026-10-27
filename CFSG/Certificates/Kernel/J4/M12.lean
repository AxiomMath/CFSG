module

public section

namespace CFSG.KJ4

@[expose] def c0 : Nat := nat_lit 5445847423328601499764522166702896582657
@[expose] def rowMask : Nat := nat_lit 4095
@[expose] def ident12 : Nat := nat_lit 11151733894906779683522195341810241573494785
@[expose] def colMask : Nat := nat_lit 2722923711664300749882261083351448291328
@[expose] def linMask : Nat := nat_lit 22298022274818958840785836011565010057689087
@[expose] def m2lo : Nat := nat_lit 33056565380087516495879
@[expose] def m2hi : Nat := nat_lit 264452523040700131967032
@[expose] def m3a : Nat := nat_lit 324518553663149093266094385266689
@[expose] def m3b : Nat := nat_lit 649037107326298186532188770533378
@[expose] def m3c : Nat := nat_lit 1298074214652596373064377541066756
@[expose] def perm3 : Nat := nat_lit 6746936868

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec false b a
@[expose] noncomputable def orB (a b : Bool) : Bool := Bool.rec b true a

@[expose] noncomputable def mulStep (A B acc k k12 : Nat) : Nat :=
  Nat.xor acc (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A k) c0) rowMask)
    (Nat.mul (Nat.land (Nat.shiftRight B k12) rowMask) c0))

@[expose] noncomputable def mul12 (A B : Nat) : Nat :=
  mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (mulStep A B (nat_lit 0) (nat_lit 0) (nat_lit 0)) (nat_lit 1) (nat_lit 12)) (nat_lit 2) (nat_lit 24)) (nat_lit 3) (nat_lit 36)) (nat_lit 4) (nat_lit 48)) (nat_lit 5) (nat_lit 60)) (nat_lit 6) (nat_lit 72)) (nat_lit 7) (nat_lit 84)) (nat_lit 8) (nat_lit 96)) (nat_lit 9) (nat_lit 108)) (nat_lit 10) (nat_lit 120)) (nat_lit 11) (nat_lit 132)

@[expose] noncomputable def sp1 (x : Nat) : Nat :=
  Nat.lor (Nat.land x (nat_lit 63)) (Nat.shiftLeft (Nat.land x (nat_lit 4032)) (nat_lit 66))
@[expose] noncomputable def sp2 (x : Nat) : Nat :=
  Nat.lor (Nat.land x m2lo) (Nat.shiftLeft (Nat.land x m2hi) (nat_lit 33))
@[expose] noncomputable def sp3 (x : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.land x m3a) (Nat.shiftLeft (Nat.land x m3b) (nat_lit 11)))
    (Nat.shiftLeft (Nat.land x m3c) (nat_lit 22))
@[expose] noncomputable def spreadS (x : Nat) : Nat := Nat.mul (sp3 (sp2 (sp1 x))) rowMask
@[expose] noncomputable def fold1 (t : Nat) : Nat := Nat.xor t (Nat.shiftRight t (nat_lit 72))
@[expose] noncomputable def fold2 (t : Nat) : Nat := Nat.xor t (Nat.shiftRight t (nat_lit 36))
@[expose] noncomputable def fold3 (t : Nat) : Nat :=
  Nat.xor t (Nat.xor (Nat.shiftRight t (nat_lit 12)) (Nat.shiftRight t (nat_lit 24)))

@[expose] noncomputable def vecmul (x M : Nat) : Nat :=
  Nat.land (fold3 (fold2 (fold1 (Nat.land (spreadS x) M)))) rowMask

@[expose] noncomputable def pv (P i : Nat) : Nat := Nat.land (Nat.shiftRight P (Nat.mul (nat_lit 12) i)) rowMask
@[expose] noncomputable def sel (h i : Nat) : Nat :=
  Nat.land (Nat.shiftRight perm3 (Nat.add (Nat.mul (nat_lit 6) h) (Nat.mul (nat_lit 2) i))) (nat_lit 3)

@[expose] noncomputable def chkPt (P g Q h : Nat) : Bool :=
  andB (Nat.blt h (nat_lit 6))
    (andB (Nat.beq (vecmul (pv P (nat_lit 0)) g) (pv Q (sel h (nat_lit 0))))
      (Nat.beq (vecmul (pv P (nat_lit 1)) g) (pv Q (sel h (nat_lit 1)))))

@[expose] noncomputable def ptOK (P : Nat) : Bool :=
  andB (Nat.blt (nat_lit 0) (pv P (nat_lit 0))) (andB (Nat.blt (pv P (nat_lit 0)) (pv P (nat_lit 1)))
    (andB (Nat.blt (pv P (nat_lit 1)) (pv P (nat_lit 2))) (andB (Nat.blt P (nat_lit 68719476736))
      (Nat.beq (Nat.xor (pv P (nat_lit 0)) (pv P (nat_lit 1))) (pv P (nat_lit 2))))))

@[expose] noncomputable def chkMul (C A B : Nat) : Bool := Nat.beq C (mul12 A B)
@[expose] noncomputable def chkInv (A B : Nat) : Bool := Nat.beq (mul12 A B) ident12
@[expose] noncomputable def chkEq (a b : Nat) : Bool := Nat.beq a b
@[expose] noncomputable def chkLt (a b : Nat) : Bool := Nat.blt a b
@[expose] noncomputable def chkTrans (A : Nat) : Bool := Nat.beq (Nat.land A linMask) ident12
@[expose] noncomputable def chkLin (A : Nat) : Bool := Nat.beq (Nat.land A colMask) (nat_lit 0)

end CFSG.KJ4

end
