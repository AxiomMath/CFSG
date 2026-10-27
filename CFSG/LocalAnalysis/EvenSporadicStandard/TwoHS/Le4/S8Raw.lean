module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Data
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Matrix

structure R4 where
  a00 : ℕ
  a01 : ℕ
  a02 : ℕ
  a03 : ℕ
  a10 : ℕ
  a11 : ℕ
  a12 : ℕ
  a13 : ℕ
  a20 : ℕ
  a21 : ℕ
  a22 : ℕ
  a23 : ℕ
  a30 : ℕ
  a31 : ℕ
  a32 : ℕ
  a33 : ℕ
  deriving DecidableEq, Inhabited

structure RV where
  v0 : ℕ
  v1 : ℕ
  v2 : ℕ
  v3 : ℕ
  deriving DecidableEq, Inhabited

@[expose] def zc (n : ℕ) : ZMod 4 := (n : ZMod 4)

@[expose] def ofR4 (a : R4) : M4 :=
  Matrix.of ![![zc a.a00, zc a.a01, zc a.a02, zc a.a03], ![zc a.a10, zc a.a11, zc a.a12, zc a.a13],
    ![zc a.a20, zc a.a21, zc a.a22, zc a.a23], ![zc a.a30, zc a.a31, zc a.a32, zc a.a33]]

@[expose] def toR4 (A : M4) : R4 :=
  ⟨(A 0 0).val, (A 0 1).val, (A 0 2).val, (A 0 3).val, (A 1 0).val, (A 1 1).val, (A 1 2).val,
    (A 1 3).val, (A 2 0).val, (A 2 1).val, (A 2 2).val, (A 2 3).val, (A 3 0).val, (A 3 1).val,
    (A 3 2).val, (A 3 3).val⟩

@[expose] def ofRV (v : RV) : V4 := ![zc v.v0, zc v.v1, zc v.v2, zc v.v3]

@[expose] def toRV (v : V4) : RV := ⟨(v 0).val, (v 1).val, (v 2).val, (v 3).val⟩

@[expose] def R4.wf (a : R4) : Prop :=
  a.a00 < 4 ∧ a.a01 < 4 ∧ a.a02 < 4 ∧ a.a03 < 4 ∧ a.a10 < 4 ∧ a.a11 < 4 ∧ a.a12 < 4 ∧
    a.a13 < 4 ∧ a.a20 < 4 ∧ a.a21 < 4 ∧ a.a22 < 4 ∧ a.a23 < 4 ∧ a.a30 < 4 ∧ a.a31 < 4 ∧
    a.a32 < 4 ∧ a.a33 < 4

instance (a : R4) : Decidable a.wf := by unfold R4.wf; infer_instance

@[expose] def RV.wf (v : RV) : Prop := v.v0 < 4 ∧ v.v1 < 4 ∧ v.v2 < 4 ∧ v.v3 < 4

instance (v : RV) : Decidable v.wf := by unfold RV.wf; infer_instance

@[expose] def rmul (a b : R4) : R4 :=
  ⟨(a.a00 * b.a00 + a.a01 * b.a10 + a.a02 * b.a20 + a.a03 * b.a30) % 4,
   (a.a00 * b.a01 + a.a01 * b.a11 + a.a02 * b.a21 + a.a03 * b.a31) % 4,
   (a.a00 * b.a02 + a.a01 * b.a12 + a.a02 * b.a22 + a.a03 * b.a32) % 4,
   (a.a00 * b.a03 + a.a01 * b.a13 + a.a02 * b.a23 + a.a03 * b.a33) % 4,
   (a.a10 * b.a00 + a.a11 * b.a10 + a.a12 * b.a20 + a.a13 * b.a30) % 4,
   (a.a10 * b.a01 + a.a11 * b.a11 + a.a12 * b.a21 + a.a13 * b.a31) % 4,
   (a.a10 * b.a02 + a.a11 * b.a12 + a.a12 * b.a22 + a.a13 * b.a32) % 4,
   (a.a10 * b.a03 + a.a11 * b.a13 + a.a12 * b.a23 + a.a13 * b.a33) % 4,
   (a.a20 * b.a00 + a.a21 * b.a10 + a.a22 * b.a20 + a.a23 * b.a30) % 4,
   (a.a20 * b.a01 + a.a21 * b.a11 + a.a22 * b.a21 + a.a23 * b.a31) % 4,
   (a.a20 * b.a02 + a.a21 * b.a12 + a.a22 * b.a22 + a.a23 * b.a32) % 4,
   (a.a20 * b.a03 + a.a21 * b.a13 + a.a22 * b.a23 + a.a23 * b.a33) % 4,
   (a.a30 * b.a00 + a.a31 * b.a10 + a.a32 * b.a20 + a.a33 * b.a30) % 4,
   (a.a30 * b.a01 + a.a31 * b.a11 + a.a32 * b.a21 + a.a33 * b.a31) % 4,
   (a.a30 * b.a02 + a.a31 * b.a12 + a.a32 * b.a22 + a.a33 * b.a32) % 4,
   (a.a30 * b.a03 + a.a31 * b.a13 + a.a32 * b.a23 + a.a33 * b.a33) % 4⟩

@[expose] def rmv (a : R4) (v : RV) : RV :=
  ⟨(a.a00 * v.v0 + a.a01 * v.v1 + a.a02 * v.v2 + a.a03 * v.v3) % 4,
   (a.a10 * v.v0 + a.a11 * v.v1 + a.a12 * v.v2 + a.a13 * v.v3) % 4,
   (a.a20 * v.v0 + a.a21 * v.v1 + a.a22 * v.v2 + a.a23 * v.v3) % 4,
   (a.a30 * v.v0 + a.a31 * v.v1 + a.a32 * v.v2 + a.a33 * v.v3) % 4⟩

@[expose] def radd (v w : RV) : RV :=
  ⟨(v.v0 + w.v0) % 4, (v.v1 + w.v1) % 4, (v.v2 + w.v2) % 4, (v.v3 + w.v3) % 4⟩

@[expose] def R4.one : R4 := ⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩

@[expose] def R4.negOne : R4 := ⟨3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3⟩

@[expose] def rsub1 (c : R4) : R4 :=
  ⟨(5 - c.a00) % 4, (4 - c.a01) % 4, (4 - c.a02) % 4, (4 - c.a03) % 4,
   (4 - c.a10) % 4, (5 - c.a11) % 4, (4 - c.a12) % 4, (4 - c.a13) % 4,
   (4 - c.a20) % 4, (4 - c.a21) % 4, (5 - c.a22) % 4, (4 - c.a23) % 4,
   (4 - c.a30) % 4, (4 - c.a31) % 4, (4 - c.a32) % 4, (5 - c.a33) % 4⟩

@[expose] def R4.mod2 (a : R4) : R4 :=
  ⟨a.a00 % 2, a.a01 % 2, a.a02 % 2, a.a03 % 2, a.a10 % 2, a.a11 % 2, a.a12 % 2, a.a13 % 2,
   a.a20 % 2, a.a21 % 2, a.a22 % 2, a.a23 % 2, a.a30 % 2, a.a31 % 2, a.a32 % 2, a.a33 % 2⟩

theorem zc_val (x : ZMod 4) : zc x.val = x := ZMod.natCast_zmod_val x

theorem val_zc (n : ℕ) : (zc n).val = n % 4 := ZMod.val_natCast 4 n

theorem ofR4_toR4 (A : M4) : ofR4 (toR4 A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofR4, toR4, zc_val]

theorem ofRV_toRV (v : V4) : ofRV (toRV v) = v := by
  ext i
  fin_cases i <;> simp [ofRV, toRV, zc_val]

theorem wf_toR4 (A : M4) : (toR4 A).wf := by
  simp only [R4.wf, toR4]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact ZMod.val_lt _

theorem wf_toRV (v : V4) : (toRV v).wf := by
  simp only [RV.wf, toRV]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> exact ZMod.val_lt _

theorem toR4_ofR4 {a : R4} (ha : a.wf) : toR4 (ofR4 a) = a := by
  obtain ⟨h00, h01, h02, h03, h10, h11, h12, h13, h20, h21, h22, h23, h30, h31, h32, h33⟩ := ha
  simp [toR4, ofR4, val_zc, Nat.mod_eq_of_lt, *]

theorem toRV_ofRV {v : RV} (hv : v.wf) : toRV (ofRV v) = v := by
  obtain ⟨h0, h1, h2, h3⟩ := hv
  simp [toRV, ofRV, val_zc, Nat.mod_eq_of_lt, *]

theorem ofR4_inj {a b : R4} (ha : a.wf) (hb : b.wf) (h : ofR4 a = ofR4 b) : a = b := by
  rw [← toR4_ofR4 ha, ← toR4_ofR4 hb, h]

theorem ofRV_inj {v w : RV} (hv : v.wf) (hw : w.wf) (h : ofRV v = ofRV w) : v = w := by
  rw [← toRV_ofRV hv, ← toRV_ofRV hw, h]

theorem ofR4_rmul (a b : R4) : ofR4 (rmul a b) = ofR4 a * ofR4 b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ofR4, rmul, zc, Matrix.mul_apply, Fin.sum_univ_four, ZMod.natCast_mod]

theorem ofRV_rmv (a : R4) (v : RV) : ofRV (rmv a v) = ofR4 a *ᵥ ofRV v := by
  ext i
  fin_cases i <;>
    simp [ofR4, ofRV, rmv, zc, Matrix.mulVec, dotProduct, Fin.sum_univ_four, ZMod.natCast_mod]

theorem ofRV_radd (v w : RV) : ofRV (radd v w) = ofRV v + ofRV w := by
  ext i
  fin_cases i <;> simp [ofRV, radd, zc, ZMod.natCast_mod]

theorem ofR4_one : ofR4 R4.one = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofR4, R4.one, zc]

theorem ofR4_negOne : ofR4 R4.negOne = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofR4, R4.negOne, zc] <;> decide

theorem wf_rmul (a b : R4) : (rmul a b).wf := by
  simp only [R4.wf, rmul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem wf_rmv (a : R4) (v : RV) : (rmv a v).wf := by
  simp only [RV.wf, rmv]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem wf_radd (v w : RV) : (radd v w).wf := by
  simp only [RV.wf, radd]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem wf_rsub1 (c : R4) : (rsub1 c).wf := by
  simp only [R4.wf, rsub1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem wf_one : R4.one.wf := by decide

theorem wf_negOne : R4.negOne.wf := by decide

theorem ofR4_rsub1 {c : R4} (hc : c.wf) : ofR4 (rsub1 c) = 1 - ofR4 c := by
  obtain ⟨h00, h01, h02, h03, h10, h11, h12, h13, h20, h21, h22, h23, h30, h31, h32, h33⟩ := hc
  have key0 : ∀ x : ℕ, x < 4 → zc ((4 - x) % 4) = 0 - zc x := by
    intro x hx
    obtain rfl | rfl | rfl | rfl : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by omega
    all_goals decide
  have key1 : ∀ x : ℕ, x < 4 → zc ((5 - x) % 4) = 1 - zc x := by
    intro x hx
    obtain rfl | rfl | rfl | rfl : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by omega
    all_goals decide
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofR4, rsub1, Matrix.sub_apply] <;>
    first | exact key0 _ ‹_› | exact key1 _ ‹_›

end CFSG.EvenSporadicStandard.TwoHS
