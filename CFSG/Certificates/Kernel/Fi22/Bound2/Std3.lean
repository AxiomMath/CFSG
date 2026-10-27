module

import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Lce
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Certificates.Kernel.Fi22.Bound.Cov
public import CFSG.Certificates.Kernel.Fi22.Bound.Rels
public import CFSG.Certificates.Kernel.Fi22.Bound.Data.Cov

public section

namespace CFSG.KC.Fi22B2.Std3

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi22B.Cov

@[expose] noncomputable def letM (A B BI l : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) BI B (Nat.beq l (nat_lit 2))) A (Nat.blt l (nat_lit 2))

@[expose] noncomputable def evalW (A B BI W n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) one4
    (fun q acc => strictN acc (fun x => mul4 x (letM A B BI (wLet W q)))) n

@[expose] noncomputable def scalarOK (X : Nat) : Bool :=
  (fun x0 x1 => andB (orB (Nat.beq x0 (nat_lit 0)) (Nat.beq x0 one4))
      (andB (orB (Nat.beq x1 (nat_lit 0)) (Nat.beq x1 one4))
        (notB (andB (Nat.beq x0 (nat_lit 0)) (Nat.beq x1 (nat_lit 0))))))
    (Nat.land X M729) (Nat.shiftRight X (nat_lit 729))

@[expose] noncomputable def relOK (A B R : Nat) : Bool :=
  scalarOK (evalW A B (pw4 B (nat_lit 12)) (wWord R) (wLen R))

theorem b_inv : Nat.beq (mul4 CFSG.KD.Fi22BC3.B (pw4 CFSG.KD.Fi22BC3.B (nat_lit 12))) one4 = true := by
  quickRfl

theorem rel0 : relOK CFSG.KD.Fi22BC3.A CFSG.KD.Fi22BC3.B (CFSG.KC.Fi22B.rel 0) = true := by quickRfl
theorem rel1 : relOK CFSG.KD.Fi22BC3.A CFSG.KD.Fi22BC3.B (CFSG.KC.Fi22B.rel 1) = true := by quickRfl
theorem rel2 : relOK CFSG.KD.Fi22BC3.A CFSG.KD.Fi22BC3.B (CFSG.KC.Fi22B.rel 2) = true := by quickRfl
theorem rel3 : relOK CFSG.KD.Fi22BC3.A CFSG.KD.Fi22BC3.B (CFSG.KC.Fi22B.rel 3) = true := by quickRfl
theorem rel4 : relOK CFSG.KD.Fi22BC3.A CFSG.KD.Fi22BC3.B (CFSG.KC.Fi22B.rel 4) = true := by quickRfl
theorem rel5 : relOK CFSG.KD.Fi22BC3.A CFSG.KD.Fi22BC3.B (CFSG.KC.Fi22B.rel 5) = true := by quickRfl
theorem rel6 : relOK CFSG.KD.Fi22BC3.A CFSG.KD.Fi22BC3.B (CFSG.KC.Fi22B.rel 6) = true := by quickRfl
theorem rel7 : relOK CFSG.KD.Fi22BC3.A CFSG.KD.Fi22BC3.B (CFSG.KC.Fi22B.rel 7) = true := by quickRfl
theorem rel8 : relOK CFSG.KD.Fi22BC3.A CFSG.KD.Fi22BC3.B (CFSG.KC.Fi22B.rel 8) = true := by quickRfl
theorem rel9 : relOK CFSG.KD.Fi22BC3.A CFSG.KD.Fi22BC3.B (CFSG.KC.Fi22B.rel 9) = true := by quickRfl
theorem rel10 : relOK CFSG.KD.Fi22BC3.A CFSG.KD.Fi22BC3.B (CFSG.KC.Fi22B.rel 10) = true := by quickRfl
theorem rel11 : relOK CFSG.KD.Fi22BC3.A CFSG.KD.Fi22BC3.B (CFSG.KC.Fi22B.rel 11) = true := by quickRfl
theorem rel12 : relOK CFSG.KD.Fi22BC3.A CFSG.KD.Fi22BC3.B (CFSG.KC.Fi22B.rel 12) = true := by quickRfl

theorem swap_rejected : notB (relOK CFSG.KD.Fi22BC3.B CFSG.KD.Fi22BC3.A (CFSG.KC.Fi22B.rel 4)) = true := by
  quickRfl

theorem ab10_rejected : notB (relOK CFSG.KD.Fi22BC3.A CFSG.KD.Fi22BC3.B
    (Nat.add (nat_lit 80) (Nat.shiftLeft (Nat.land (Nat.shiftRight (CFSG.KC.Fi22B.rel 2) (nat_lit 12))
      (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 160)) (nat_lit 1))) (nat_lit 12)))) = true := by
  quickRfl

end CFSG.KC.Fi22B2.Std3

end
