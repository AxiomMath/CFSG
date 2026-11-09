module

public import Certificates.Data.CFSGNative.He.Fp
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.KS.SporSch

open CFSG.Sporadic.He.Native

@[expose] def toM5 (X : Array (Array ℕ)) : Matrix (Fin 133) (Fin 133) (ZMod 5) :=
  Matrix.of fun i j => (((X[i.val]!)[j.val]! : ℕ) : ZMod 5)

@[expose] def ofM5 (M : Matrix (Fin 133) (Fin 133) (ZMod 5)) : Array (Array ℕ) :=
  Array.ofFn fun i => Array.ofFn fun j => (M i j).val

theorem ofFn_getElem!5 {α : Type*} [Inhabited α] {n : ℕ} (f : Fin n → α) {i : ℕ} (hi : i < n) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

theorem toM5_ofM5 (M : Matrix (Fin 133) (Fin 133) (ZMod 5)) : toM5 (ofM5 M) = M := by
  ext i j
  unfold toM5 ofM5
  simp only [Matrix.of_apply]
  rw [ofFn_getElem!5 _ i.isLt, ofFn_getElem!5 _ j.isLt]
  exact ZMod.natCast_zmod_val (M i j)

theorem fold_sum5 (g : ℕ → ℕ) : ∀ n, Nat.fold n (fun j _ acc => acc + g j) 0 =
    ∑ j ∈ Finset.range n, g j
  | 0 => by rw [Nat.fold_zero, Finset.sum_range_zero]
  | n + 1 => by
    rw [Nat.fold_succ, Finset.sum_range_succ, ← fold_sum5 g n]

theorem mulM5_eq (X Y : Array (Array ℕ)) : mulM 5 133 X Y = ofM5 (toM5 X * toM5 Y) := by
  unfold mulM ofM5
  refine congrArg Array.ofFn (funext fun i => congrArg Array.ofFn (funext fun k => ?_))
  unfold dot
  rw [Matrix.mul_apply]
  have e : ∀ j : ℕ, j < 133 → (col 133 Y k.val)[j]! = (Y[j]!)[k.val]! := by
    intro j hj
    unfold col
    rw [ofFn_getElem!5 _ hj]
  have h1 : Nat.fold 133 (fun j _ acc => acc + (X[i.val]!)[j]! * (col 133 Y k.val)[j]!) 0 =
      ∑ j ∈ Finset.range 133, (X[i.val]!)[j]! * (Y[j]!)[k.val]! := by
    rw [fold_sum5 (fun j => (X[i.val]!)[j]! * (col 133 Y k.val)[j]!) 133]
    exact Finset.sum_congr rfl fun j hj => by rw [e j (Finset.mem_range.1 hj)]
  rw [h1]
  have h2 : (∑ j : Fin 133, toM5 X i j * toM5 Y j k) =
      ((∑ j ∈ Finset.range 133, (X[i.val]!)[j]! * (Y[j]!)[k.val]! : ℕ) : ZMod 5) := by
    rw [Nat.cast_sum, ← Fin.sum_univ_eq_sum_range
      (fun j => (((X[i.val]!)[j]! * (Y[j]!)[k.val]! : ℕ) : ZMod 5)) 133]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [toM5]
  rw [h2, ZMod.val_natCast]

theorem mulM5_assoc (X Y Z : Array (Array ℕ)) :
    mulM 5 133 (mulM 5 133 X Y) Z = mulM 5 133 X (mulM 5 133 Y Z) := by
  rw [mulM5_eq X Y, mulM5_eq Y Z, mulM5_eq, mulM5_eq, toM5_ofM5, toM5_ofM5, Matrix.mul_assoc]

theorem powM5_add {M : Array (Array ℕ)} (hM : mulM 5 133 (idM 133) M = M) (a : ℕ) :
    ∀ b, 1 ≤ b → powM 5 133 M (a + b) = mulM 5 133 (powM 5 133 M a) (powM 5 133 M b) := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base =>
    change mulM 5 133 (powM 5 133 M a) M = mulM 5 133 (powM 5 133 M a) (mulM 5 133 (idM 133) M)
    rw [hM]
  | succ b hb ih =>
    change mulM 5 133 (powM 5 133 M (a + b)) M =
      mulM 5 133 (powM 5 133 M a) (mulM 5 133 (powM 5 133 M b) M)
    rw [ih, mulM5_assoc]

end CFSG.KS.SporSch

end
