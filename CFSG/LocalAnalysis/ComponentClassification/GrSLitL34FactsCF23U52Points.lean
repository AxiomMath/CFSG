module

public import CFSG.Fischer.F4
import all CFSG.Fischer.F4
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.ComponentClassification.GSThmB.U52

open CFSG.Fischer Matrix

abbrev V : Type := Fin 5 → F4

@[expose] def lead (v : V) : F4 :=
  if v 0 ≠ 0 then v 0 else if v 1 ≠ 0 then v 1 else if v 2 ≠ 0 then v 2 else
    if v 3 ≠ 0 then v 3 else v 4

@[expose] def normalize (v : V) : V := (lead v)⁻¹ • v

@[expose] def code (a : F4) : ℕ := a.code.val

@[expose] def rawIndex (v : V) : ℕ :=
  if v 0 ≠ 0 then 64 * code (v 1) + 16 * code (v 2) + 4 * code (v 3) + code (v 4)
  else if v 1 ≠ 0 then 256 + 16 * code (v 2) + 4 * code (v 3) + code (v 4)
  else if v 2 ≠ 0 then 320 + 4 * code (v 3) + code (v 4)
  else if v 3 ≠ 0 then 336 + code (v 4) else 340

@[expose] def ptIndex (v : V) : ℕ := rawIndex (normalize v)

@[expose] def uncode (c : ℕ) : F4 := ⟨⟨c % 4, Nat.mod_lt _ (by norm_num)⟩⟩

@[expose] def decode (i : ℕ) : V :=
  if i < 256 then ![1, uncode (i / 64), uncode (i / 16 % 4), uncode (i / 4 % 4), uncode (i % 4)]
  else if i < 320 then
    ![0, 1, uncode ((i - 256) / 16), uncode ((i - 256) / 4 % 4), uncode ((i - 256) % 4)]
  else if i < 336 then ![0, 0, 1, uncode ((i - 320) / 4), uncode ((i - 320) % 4)]
  else if i < 340 then ![0, 0, 0, 1, uncode (i - 336)] else ![0, 0, 0, 0, 1]

theorem code_lt (a : F4) : code a < 4 := a.code.isLt

theorem rawIndex_lt (v : V) : rawIndex v < 341 := by
  have := code_lt (v 1)
  have := code_lt (v 2)
  have := code_lt (v 3)
  have := code_lt (v 4)
  unfold rawIndex
  split_ifs <;> omega

theorem ptIndex_lt (v : V) : ptIndex v < 341 := rawIndex_lt _

theorem lead_smul {t : F4} (ht : t ≠ 0) (v : V) : lead (t • v) = t * lead v := by
  simp only [lead, Pi.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, ht, false_or]
  split_ifs <;> rfl

theorem normalize_smul {t : F4} (ht : t ≠ 0) (v : V) : normalize (t • v) = normalize v := by
  rw [normalize, normalize, lead_smul ht, smul_smul, mul_inv, mul_comm t⁻¹, mul_assoc,
    inv_mul_cancel₀ ht, mul_one]

theorem ptIndex_smul {t : F4} (ht : t ≠ 0) (v : V) : ptIndex (t • v) = ptIndex v := by
  rw [ptIndex, ptIndex, normalize_smul ht]

theorem decode_ne_zero (i : ℕ) : decode i ≠ 0 := by
  intro h
  unfold decode at h
  split_ifs at h
  · exact one_ne_zero (congrFun h 0)
  · exact one_ne_zero (congrFun h 1)
  · exact one_ne_zero (congrFun h 2)
  · exact one_ne_zero (congrFun h 3)
  · exact one_ne_zero (congrFun h 4)

theorem ptIndex_decode : ∀ i : Fin 341, ptIndex (decode i) = i := by
  decide +kernel

@[expose] def mv5 (A : Matrix (Fin 5) (Fin 5) F4) (v : V) : V :=
  fun i => A i 0 * v 0 + A i 1 * v 1 + A i 2 * v 2 + A i 3 * v 3 + A i 4 * v 4

theorem mulVec_eq_mv5 (A : Matrix (Fin 5) (Fin 5) F4) (v : V) : A *ᵥ v = mv5 A v := by
  funext i
  simp [mulVec, dotProduct, Fin.sum_univ_five, mv5]

@[expose] def matN (k : ℕ) : Matrix (Fin 5) (Fin 5) F4 :=
  Matrix.of fun i j => uncode (k / 4 ^ (5 * i.val + j.val))

@[expose] def tabN (k : ℕ) : Array ℕ :=
  Array.ofFn (n := 341) fun i => ptIndex (mv5 (matN k) (decode i.val))

@[expose] def frobTab : Array ℕ :=
  Array.ofFn (n := 341) fun i => ptIndex fun j => decode i.val j * decode i.val j

theorem tabN_getElem! (k : ℕ) (i : Fin 341) :
    (tabN k)[(i : ℕ)]! = ptIndex (matN k *ᵥ decode i) := by
  rw [tabN, getElem!_pos _ _ (by simp), Array.getElem_ofFn, mulVec_eq_mv5]

end CFSG.ComponentClassification.GSThmB.U52
