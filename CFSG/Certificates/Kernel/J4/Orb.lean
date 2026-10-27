module

public import CFSG.Certificates.Kernel.J4.M12

public section

namespace CFSG.KJ4

@[expose] noncomputable def lv (L k : Nat) : Nat := Nat.land (Nat.shiftRight L (Nat.mul (nat_lit 12) k)) rowMask
@[expose] noncomputable def lpar (PG k : Nat) : Nat := Nat.land (Nat.shiftRight PG (Nat.mul (nat_lit 24) k)) (nat_lit 65535)
@[expose] noncomputable def lgen (PG k : Nat) : Nat :=
  Nat.land (Nat.shiftRight PG (Nat.add (Nat.mul (nat_lit 24) k) (nat_lit 16))) (nat_lit 255)
@[expose] noncomputable def gmat (G g : Nat) : Nat :=
  Nat.land (Nat.shiftRight G (Nat.mul (nat_lit 144) g)) (nat_lit 22300745198530623141535718272648361505980415)

@[expose] noncomputable def orAll (L n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (lv L k))) n

@[expose] noncomputable def treeOK (L PG G n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k acc => andB acc (orB (Nat.beq k (nat_lit 0))
    (andB (Nat.blt (lpar PG k) k) (Nat.beq (vecmul (lv L (lpar PG k)) (gmat G (lgen PG k))) (lv L k))))) n

@[expose] noncomputable def swarMask (n b : Nat) : Nat :=
  Nat.mul (Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 2) b)) (nat_lit 1)))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) b) (nat_lit 1))

@[expose] noncomputable def swarStep (n b x : Nat) : Nat :=
  Nat.add (Nat.land x (swarMask n b)) (Nat.land (Nat.shiftRight x b) (swarMask n b))

@[expose] noncomputable def popcount (x n : Nat) : Nat :=
  Nat.land (Nat.shiftRight (Nat.mul (swarStep n (nat_lit 16) (swarStep n (nat_lit 8)
      (swarStep n (nat_lit 4) (swarStep n (nat_lit 2) (swarStep n (nat_lit 1) x)))))
    (Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1)) (nat_lit 4294967295)))
    (Nat.sub n (nat_lit 32))) (nat_lit 4294967295)

@[expose] noncomputable def orbOK (L PG G n : Nat) : Bool :=
  andB (Nat.beq (popcount (orAll L n) (nat_lit 4096)) n) (treeOK L PG G n)

@[expose] noncomputable def chkFix (v g : Nat) : Bool := Nat.beq (vecmul v g) v

@[expose] noncomputable def chkVec (w v g : Nat) : Bool := Nat.beq (vecmul v g) w

end CFSG.KJ4

end
