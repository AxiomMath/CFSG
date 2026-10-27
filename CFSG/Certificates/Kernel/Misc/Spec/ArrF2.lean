module

public import CFSG.LieType.Multipliers.G23Data
public import CFSG.Certificates.Kernel.Misc.Spec.F2Blow

public section

namespace CFSG.KC.Misc.Spec

open CFSG.Sporadic.He.Native CFSG.LieType.Multipliers.G23

@[expose] def toM (X : Array (Array ℕ)) : Matrix (Fin 54) (Fin 54) (ZMod 2) :=
  Matrix.of fun i j => (((X[i.val]!)[j.val]! : ℕ) : ZMod 2)

@[expose] def ofM (M : Matrix (Fin 54) (Fin 54) (ZMod 2)) : Array (Array ℕ) :=
  Array.ofFn fun i => Array.ofFn fun j => (M i j).val

theorem val_one_two : (1 : ZMod 2).val = 1 := rfl

theorem ofFn_getElem! {α : Type*} [Inhabited α] {n : ℕ} (f : Fin n → α) {i : ℕ} (hi : i < n) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

theorem toM_ofM (M : Matrix (Fin 54) (Fin 54) (ZMod 2)) : toM (ofM M) = M := by
  ext i j
  unfold toM ofM
  simp only [Matrix.of_apply]
  rw [ofFn_getElem! _ i.isLt, ofFn_getElem! _ j.isLt]
  exact ZMod.natCast_zmod_val (M i j)

theorem fold_sum (g : ℕ → ℕ) : ∀ n, Nat.fold n (fun j _ acc => acc + g j) 0 =
    ∑ j ∈ Finset.range n, g j
  | 0 => by rw [Nat.fold_zero, Finset.sum_range_zero]
  | n + 1 => by
    rw [Nat.fold_succ, Finset.sum_range_succ, ← fold_sum g n]

theorem mulM_eq (X Y : Array (Array ℕ)) : mulM 2 54 X Y = ofM (toM X * toM Y) := by
  unfold mulM ofM
  refine congrArg Array.ofFn (funext fun i => congrArg Array.ofFn (funext fun k => ?_))
  unfold dot
  rw [Matrix.mul_apply]
  have e : ∀ j : ℕ, j < 54 → (col 54 Y k.val)[j]! = (Y[j]!)[k.val]! := by
    intro j hj
    unfold col
    rw [ofFn_getElem! _ hj]
  have h1 : Nat.fold 54 (fun j _ acc => acc + (X[i.val]!)[j]! * (col 54 Y k.val)[j]!) 0 =
      ∑ j ∈ Finset.range 54, (X[i.val]!)[j]! * (Y[j]!)[k.val]! := by
    rw [fold_sum (fun j => (X[i.val]!)[j]! * (col 54 Y k.val)[j]!) 54]
    exact Finset.sum_congr rfl fun j hj => by rw [e j (Finset.mem_range.1 hj)]
  rw [h1]
  have h2 : (∑ j : Fin 54, toM X i j * toM Y j k) =
      ((∑ j ∈ Finset.range 54, (X[i.val]!)[j]! * (Y[j]!)[k.val]! : ℕ) : ZMod 2) := by
    rw [Nat.cast_sum, ← Fin.sum_univ_eq_sum_range
      (fun j => (((X[i.val]!)[j]! * (Y[j]!)[k.val]! : ℕ) : ZMod 2)) 54]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [toM]
  rw [h2, ZMod.val_natCast]

theorem idM_eq : idM 54 = ofM 1 := by
  unfold idM ofM
  refine congrArg Array.ofFn (funext fun i => congrArg Array.ofFn (funext fun j => ?_))
  rw [Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp [val_one_two]
  · have h' : ¬ i.val = j.val := fun e => h (Fin.ext e)
    simp [h, h']

theorem blowUp_entry (M : Array (Array ℕ)) (i j : Fin 54) :
    ((blowUp M)[i.val]!)[j.val]! =
      blockEntry ((M[i.val / 2]!)[j.val / 2]!) (i.val % 2) (j.val % 2) := by
  unfold blowUp
  rw [ofFn_getElem! _ i.isLt]
  rw [ofFn_getElem! _ j.isLt]

theorem blowUp_eq (M : Array (Array ℕ)) : blowUp M = ofM (toM (blowUp M)) := by
  unfold ofM
  conv_lhs => unfold blowUp
  refine congrArg Array.ofFn (funext fun i => congrArg Array.ofFn (funext fun j => ?_))
  have h1 : toM (blowUp M) i j = ((blockEntry ((M[i.val / 2]!)[j.val / 2]!) (i.val % 2)
      (j.val % 2) : ℕ) : ZMod 2) := by
    show ((((blowUp M)[i.val]!)[j.val]! : ℕ) : ZMod 2) = _
    rw [blowUp_entry]
  rw [h1, ZMod.val_natCast]
  have hlt : blockEntry ((M[i.val / 2]!)[j.val / 2]!) (i.val % 2) (j.val % 2) < 2 :=
    blk_lt _ _ _
  rw [Nat.mod_eq_of_lt hlt]

theorem foldr_mulM {α : Type*} (L : α → Array (Array ℕ)) (w : List α) :
    w.foldr (fun l M => mulM 2 54 (L l) M) (idM 54) = ofM (wordProd (fun l => toM (L l)) w) := by
  induction w with
  | nil => exact idM_eq
  | cons l w ih =>
    rw [List.foldr_cons, ih, mulM_eq, toM_ofM]
    rfl

theorem ofM_zero_one (Z : Matrix (Fin 54) (Fin 54) (ZMod 2)) :
    ((ofM Z)[0]!)[1]! = (Z 0 1).val := by
  unfold ofM
  rw [ofFn_getElem! _ (by norm_num : 0 < 54), ofFn_getElem! _ (by norm_num : 1 < 54)]
  rfl

end CFSG.KC.Misc.Spec

end
