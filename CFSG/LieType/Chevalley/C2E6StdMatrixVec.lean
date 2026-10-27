module

public import CFSG.LieType.Chevalley.C2E6UnitaryFourDefs
public import Certificates.Data.CFSGNative.Chevalley.C2E6StdMatrix
public import CFSG.Fischer.F4
import all CFSG.Fischer.F4
public import Mathlib.Data.LawfulXor.Basic
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.LieType.Chevalley.C2E6Std.MatrixModel

open CFSG.LieType.Chevalley.C2E6Overlap

@[expose] def ofBits (b0 b1 : Bool) : K :=
  (⟨⟨(if b0 then 1 else 0) + (if b1 then 2 else 0), by split_ifs <;> decide⟩⟩ : CFSG.Fischer.F4)

@[expose] def vecOf (v : Native.Vec) (k : Fin 78) : K := ofBits (v.1.testBit k) (v.2.testBit k)

@[expose] def toMat (P : Native.Mat) : Matrix (Fin 78) (Fin 78) K :=
  Matrix.of fun k l => vecOf (P.getD l (0, 0)) k

theorem ofBits_add (a b c d : Bool) : ofBits (a ^^ c) (b ^^ d) = ofBits a b + ofBits c d := by
  revert a b c d; decide

theorem ofBits_mul (a b c d : Bool) :
    ofBits ((a && c) ^^ (b && d)) ((a && d) ^^ (b && (c ^^ d))) = ofBits a b * ofBits c d := by
  revert a b c d; decide

theorem ofBits_false : ofBits false false = 0 := by decide

theorem ofBits_true_false : ofBits true false = 1 := by decide

theorem ofBits_sq (a b : Bool) : ofBits (a ^^ b) b = ofBits a b ^ 2 := by
  revert a b; decide

theorem ofBits_injective {a b c d : Bool} (h : ofBits a b = ofBits c d) : a = c ∧ b = d := by
  revert a b c d h; decide

theorem vecOf_vadd (u v : Native.Vec) : vecOf (Native.vadd u v) = vecOf u + vecOf v := by
  funext k
  simp only [vecOf, Native.vadd, Nat.testBit_xor, Pi.add_apply, ofBits_add]

private theorem testBit_ite (c : Bool) (m k : ℕ) :
    (if c then m else 0).testBit k = (c && m.testBit k) := by
  cases c <;> simp

theorem vecOf_vsmul (c0 c1 : Bool) (v : Native.Vec) :
    vecOf (Native.vsmul c0 c1 v) = ofBits c0 c1 • vecOf v := by
  funext k
  simp only [vecOf, Native.vsmul, Nat.testBit_xor, testBit_ite, Pi.smul_apply, smul_eq_mul,
    ← ofBits_mul]

theorem vecOf_zero : vecOf (0, 0) = 0 := by
  funext k
  simp [vecOf, ofBits_false]

theorem vecOf_applyAux (P : Native.Mat) (u : Native.Vec) (n : ℕ) (acc : Native.Vec) :
    vecOf (Native.applyAux P u n acc) =
      vecOf acc + ∑ m ∈ Finset.range n, ofBits (u.1.testBit m) (u.2.testBit m) •
        vecOf (P.getD m (0, 0)) := by
  induction n with
  | zero => simp [Native.applyAux]
  | succ n ih => rw [Native.applyAux, vecOf_vadd, ih, vecOf_vsmul, Finset.sum_range_succ, add_assoc]

theorem vecOf_apply (P : Native.Mat) (u : Native.Vec) (k : Fin 78) :
    vecOf (Native.apply P u) k = ∑ m : Fin 78, vecOf (P.getD m (0, 0)) k * vecOf u m := by
  rw [Native.apply, vecOf_applyAux, vecOf_zero, zero_add, Finset.sum_apply, Finset.sum_range]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [vecOf, mul_comm]

theorem apply_zero (P : Native.Mat) : Native.apply P (0, 0) = (0, 0) := by
  have h : ∀ n, Native.applyAux P (0, 0) n (0, 0) = (0, 0) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp [Native.applyAux, ih, Native.vadd, Native.vsmul]
  exact h 78

theorem getD_map_of {f : Native.Vec → Native.Vec} (hf : f (0, 0) = (0, 0)) (Q : Native.Mat)
    (l : ℕ) : (Q.map f).getD l (0, 0) = f (Q.getD l (0, 0)) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases Q[l]? <;> simp [hf]

theorem toMat_mul (P Q : Native.Mat) : toMat (Native.mul P Q) = toMat P * toMat Q := by
  ext k l
  rw [Matrix.mul_apply]
  simp only [toMat, Native.mul, Matrix.of_apply]
  rw [getD_map_of (apply_zero P), vecOf_apply]

theorem toMat_one : toMat Native.one = 1 := by
  ext k l
  simp only [toMat, Native.one, Matrix.of_apply, Matrix.one_apply]
  have hl : ((List.range 78).toArray.map fun l => ((1 <<< l : ℕ), (0 : ℕ))).getD l (0, 0) =
      (1 <<< (l : ℕ), 0) := by
    simp [Array.getD_eq_getD_getElem?, l.2]
  rw [hl]
  simp only [vecOf, Nat.one_shiftLeft, Nat.testBit_two_pow, Nat.zero_testBit]
  by_cases h : k = l
  · subst h; simp [ofBits_true_false]
  · have h' : (l : ℕ) ≠ k := fun e => h (Fin.ext e.symm)
    simp [h, h', ofBits_false]

theorem toMat_eq_of_eqM {P Q : Native.Mat} (h : Native.eqM P Q = true) : toMat P = toMat Q := by
  ext k l
  simp only [Native.eqM, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h l l.2 k k.2
  simp only [toMat, vecOf, Matrix.of_apply]
  rw [h1, h2]

theorem eqM_of_toMat_eq {P Q : Native.Mat} (h : toMat P = toMat Q) : Native.eqM P Q = true := by
  simp only [Native.eqM, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq]
  intro l hl k hk
  have e := congrFun (congrFun h ⟨k, hk⟩) ⟨l, hl⟩
  simp only [toMat, vecOf, Matrix.of_apply] at e
  exact ofBits_injective e

theorem toMat_pow (P : Native.Mat) (n : ℕ) : toMat (Native.pow P n) = toMat P ^ n := by
  induction n with
  | zero => exact toMat_one
  | succ n ih => rw [Native.pow, toMat_mul, ih, pow_succ]

end CFSG.LieType.Chevalley.C2E6Std.MatrixModel
