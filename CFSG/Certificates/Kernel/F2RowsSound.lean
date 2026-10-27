module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs
public import Certificates.Data.Kernel.F2Rows

public section

namespace CFSG.KC.F2Rows

open Matrix Finset

variable {ι κ ν : Type*} {m n p : ℕ}

@[expose] def bitMat (e₁ : ι ≃ Fin m) (e₂ : κ ≃ Fin n) (R : List ℕ) : Matrix ι κ (ZMod 2) :=
  fun i k => if (R.getD (e₁ i) 0).testBit (e₂ k) then 1 else 0

@[expose] def rowsOf (e₁ : ι ≃ Fin m) (e₂ : κ ≃ Fin n) (M : Matrix ι κ (ZMod 2)) : List ℕ :=
  (List.range m).map fun i => ofBitsF n fun j =>
    if hi : i < m then (if hj : j < n then decide (M (e₁.symm ⟨i, hi⟩) (e₂.symm ⟨j, hj⟩) = 1)
      else false) else false

@[expose] def bitZ (x j : ℕ) : ZMod 2 := if x.testBit j then 1 else 0

theorem bitZ_xor (a b j : ℕ) : bitZ (a ^^^ b) j = bitZ a j + bitZ b j := by
  unfold bitZ
  rw [Nat.testBit_xor]
  cases a.testBit j <;> cases b.testBit j <;> decide

theorem bitZ_zero (j : ℕ) : bitZ 0 j = 0 := by
  simp [bitZ]

theorem testBit_ofBitsF (g : ℕ → Bool) (i : ℕ) :
    (ofBitsF n g).testBit i = (decide (i < n) && g i) := by
  unfold ofBitsF
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    split_ifs with hf
    · rw [Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
      by_cases him : i = n
      · subst him
        simp [hf]
      · have h1 : (i < n + 1) ↔ (i < n) := by omega
        simp [h1, Ne.symm him]
    · rw [ih]
      by_cases him : i = n
      · subst him
        simp [hf]
      · have h1 : (i < n + 1) ↔ (i < n) := by omega
        simp [h1]

theorem getD_range_map (g : ℕ → ℕ) {i : ℕ} (hi : i < m) :
    ((List.range m).map g).getD i 0 = g i := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem getD_map_zero (f : ℕ → ℕ) (hf : f 0 = 0) (l : List ℕ) (i : ℕ) :
    (l.map f).getD i 0 = f (l.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? with
  | none => exact hf.symm
  | some a => rfl

theorem zmod_two_ite (x : ZMod 2) : (if x = 1 then (1 : ZMod 2) else 0) = x := by
  revert x
  decide

theorem bitMat_rowsOf (e₁ : ι ≃ Fin m) (e₂ : κ ≃ Fin n) (M : Matrix ι κ (ZMod 2)) :
    bitMat e₁ e₂ (rowsOf e₁ e₂ M) = M := by
  funext i k
  unfold bitMat rowsOf
  rw [getD_range_map _ (e₁ i).isLt, testBit_ofBitsF]
  simp only [(e₁ i).isLt, (e₂ k).isLt, decide_true, Bool.true_and, dite_true, Fin.eta,
    Equiv.symm_apply_apply, decide_eq_true_eq]
  exact zmod_two_ite _

theorem bitZ_foldl (Y : List ℕ) (x j acc : ℕ) (n : ℕ) :
    bitZ ((List.range n).foldl (fun acc t => if x.testBit t then acc ^^^ Y.getD t 0 else acc) acc)
      j = bitZ acc j + ∑ t ∈ range n, bitZ x t * bitZ (Y.getD t 0) j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, sum_range_succ,
      ← add_assoc, ← ih]
    by_cases h : x.testBit n = true
    · have hx : bitZ x n = 1 := by simp [bitZ, h]
      rw [if_pos h, bitZ_xor, hx, one_mul]
    · have hx : bitZ x n = 0 := by simp [bitZ, h]
      rw [if_neg h, hx, zero_mul, add_zero]

theorem xorRow_zero (Y : List ℕ) : xorRow n Y 0 = 0 := by
  unfold xorRow
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    simp

theorem bitMat_mul [Fintype κ] (e₁ : ι ≃ Fin m) (e₂ : κ ≃ Fin n) (e₃ : ν ≃ Fin p)
    (X Y : List ℕ) : bitMat e₁ e₂ X * bitMat e₂ e₃ Y = bitMat e₁ e₃ (mulR n X Y) := by
  funext i l
  rw [Matrix.mul_apply]
  have hg : (mulR n X Y).getD (e₁ i) 0 = xorRow n Y (X.getD (e₁ i) 0) :=
    getD_map_zero _ (xorRow_zero Y) X _
  change ∑ k, bitZ (X.getD (e₁ i) 0) (e₂ k) * bitZ (Y.getD (e₂ k) 0) (e₃ l) =
    bitZ ((mulR n X Y).getD (e₁ i) 0) (e₃ l)
  rw [hg]
  unfold xorRow
  rw [bitZ_foldl, bitZ_zero, zero_add]
  rw [Equiv.sum_comp e₂ (fun t : Fin n => bitZ (X.getD (e₁ i) 0) t * bitZ (Y.getD t 0) (e₃ l))]
  exact Fin.sum_univ_eq_sum_range (fun t => bitZ (X.getD (e₁ i) 0) t * bitZ (Y.getD t 0) (e₃ l)) n

theorem bitMat_add (e₁ : ι ≃ Fin m) (e₂ : κ ≃ Fin n) (X Y : List ℕ) :
    bitMat e₁ e₂ X + bitMat e₁ e₂ Y = bitMat e₁ e₂ (addR m X Y) := by
  funext i k
  change bitZ (X.getD (e₁ i) 0) (e₂ k) + bitZ (Y.getD (e₁ i) 0) (e₂ k) =
    bitZ ((addR m X Y).getD (e₁ i) 0) (e₂ k)
  unfold addR
  rw [getD_range_map _ (e₁ i).isLt, bitZ_xor]

theorem bitMat_idR [DecidableEq ι] (e : ι ≃ Fin m) : bitMat e e (idR m) = 1 := by
  funext i j
  rw [Matrix.one_apply]
  unfold bitMat idR
  rw [getD_range_map _ (e i).isLt, Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : i = j
  · subst h
    simp
  · have h' : (e i : ℕ) ≠ e j := fun h2 => h (e.injective (Fin.ext h2))
    simp [h, h']

end CFSG.KC.F2Rows
