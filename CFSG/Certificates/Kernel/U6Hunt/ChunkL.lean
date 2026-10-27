module

public import Certificates.Data.Kernel.U6.M22CntL
public import Certificates.Data.Kernel.Spor.Chain
import CFSG.Certificates.Kernel.Spor.PK.Perm.Comp
import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

namespace CFSG.KC.U6

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KS
open CFSG.KC.Enum (pcomp pg)

private theorem strictN_u6 (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem cntVecA_eq (R8 R0 RY : Nat) (L8 L0 LY : List Nat) {ap : Nat → Nat} {x : Nat}
    (h : ∀ i, ap i = ap5 x i) : cntVecA R8 R0 RY L8 L0 LY ap x = cntVec R8 R0 RY L8 L0 LY x := by
  have e : ap = fun i => ap5 x i := funext h
  subst e
  rfl

theorem ap5_pg (x i : Nat) : ap5 x i = pg 5 (mask 5) x i := by
  change Nat.land (Nat.shiftRight x (i * 5)) (maskN 5) = Nat.land (Nat.shiftRight x (5 * i)) (mask 5)
  rw [Nat.mul_comm]
  rfl

theorem fld5 (x j : Nat) :
    Nat.land (Nat.shiftRight x (Nat.mul (nat_lit 5) j)) (nat_lit 31) = ap5 x j := by
  rw [ap5_pg]
  rfl

theorem pc22_eq (p q : Nat) : pc22 p q = pcomp (nat_lit 22) (nat_lit 5) (mask 5) p q := by
  unfold pc22
  rw [strictN_u6, strictN_u6]
  rfl

theorem ap5_big {X i : Nat} (hX : X < 2 ^ (5 * 22)) (hi : ¬ i < 22) : ap5 X i = 0 := by
  change Nat.land (Nat.shiftRight X (i * 5)) (maskN 5) = 0
  have e : Nat.shiftRight X (i * 5) = 0 := by
    change X >>> (i * 5) = 0
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hX (Nat.pow_le_pow_right (by decide) (by omega)))
  rw [e]
  exact Nat.zero_and _

theorem ap5_pc22 (p q i : Nat) :
    ap5 (pc22 p q) i = if i < 22 then ap5 p (ap5 q i) else 0 := by
  rw [pc22_eq]
  by_cases hi : i < 22
  · rw [if_pos hi, ap5_pg, ap5_pg, ap5_pg]
    exact CFSG.KS.PF.pg_pcomp (n := 22) (by decide) hi
  · rw [if_neg hi]
    exact ap5_big (CFSG.KS.PK.pcomp_lt (n := 22) (by decide) 5 p q) hi

theorem apF_eq (p q i : Nat) : apF p q i = ap5 (pc22 p q) i := by
  rw [ap5_pc22]
  unfold apF
  by_cases hi : i < 22
  · have hb : Nat.blt i (nat_lit 22) = true := Nat.ble_eq_true_of_le hi
    rw [hb, if_pos hi]
    change Nat.land (Nat.shiftRight p (Nat.mul (nat_lit 5)
      (Nat.land (Nat.shiftRight q (Nat.mul (nat_lit 5) i)) (nat_lit 31)))) (nat_lit 31) = _
    rw [fld5, fld5]
  · have hb : Nat.blt i (nat_lit 22) = false := by
      rw [Bool.eq_false_iff]
      intro h'
      exact hi (Nat.le_of_ble_eq_true h')
    rw [hb, if_neg hi]

theorem ap3_eq (y d t i : Nat) : ap3 y d t i = ap5 (pc22 (pc22 y d) t) i := by
  rw [ap5_pc22]
  unfold ap3
  by_cases hi : i < 22
  · have hb : Nat.blt i (nat_lit 22) = true := Nat.ble_eq_true_of_le hi
    rw [hb, if_pos hi]
    change apF y d (Nat.land (Nat.shiftRight t (Nat.mul (nat_lit 5) i)) (nat_lit 31)) = _
    rw [fld5, apF_eq]
  · have hb : Nat.blt i (nat_lit 22) = false := by
      rw [Bool.eq_false_iff]
      intro h'
      exact hi (Nat.le_of_ble_eq_true h')
    rw [hb, if_neg hi]

theorem chunkL_eq (R8 R0 RY : Nat) (L8 L0 LY : List Nat) (TR : Nat → Nat) (o a : Nat) :
    chunkL R8 R0 RY L8 L0 LY TR o a = chunkK R8 R0 RY L8 L0 LY TR o a := by
  unfold chunkL chunkK
  simp only [strictN_u6]
  refine congrArg (sumN (nat_lit 21)) (funext fun b => ?_)
  refine congrArg (sumN (nat_lit 20)) (funext fun c => ?_)
  refine congrArg (sumN (nat_lit 16)) (funext fun d => ?_)
  refine congrArg (sumN (nat_lit 3)) (funext fun e => ?_)
  exact cntVecA_eq _ _ _ _ _ _ fun i => ap3_eq _ _ _ i

end CFSG.KC.U6

end
