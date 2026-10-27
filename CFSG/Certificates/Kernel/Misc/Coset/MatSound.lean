module

public import Certificates.Data.Kernel.Misc.Coset.Mat

public section

namespace CFSG.KC.MiscCoset.Mat

theorem nthN_eq (l : List Nat) (k : Nat) : nthN l k = l.getD k 0 := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    cases k with
    | zero => rfl
    | succ k =>
      rw [List.getD_cons_succ]
      exact ih k

theorem nthR_eq (X : List (List Nat)) (i : Nat) : nthR X i = X.getD i [] := by
  induction X generalizing i with
  | nil => rfl
  | cons r X ih =>
    cases i with
    | zero => rfl
    | succ i =>
      rw [List.getD_cons_succ]
      exact ih i

theorem buildL_eq {α : Type} (d : Nat) (f : Nat → α) (s : Nat) :
    buildL d f s = (List.range d).map fun i => f (s + i) := by
  induction d generalizing s with
  | zero => rfl
  | succ d ih =>
    change f s :: buildL d f (s + 1) = _
    rw [ih, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [Nat.add_zero, List.cons.injEq, true_and]
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply]
    congr 1
    omega

theorem getD_buildL {α : Type} (d : Nat) (f : Nat → α) (x : α) {i : Nat} (hi : i < d) :
    (buildL d f 0).getD i x = f i := by
  simp [buildL_eq, List.getD_eq_getElem?_getD, List.getElem?_range hi]

theorem length_buildL {α : Type} (d : Nat) (f : Nat → α) (s : Nat) : (buildL d f s).length = d := by
  simp [buildL_eq]

theorem dotN_eq (r : List Nat) (Y : List (List Nat)) (k : Nat) :
    dotN r Y k = ∑ t ∈ Finset.range Y.length, nthN r t * nthN (nthR Y t) k := by
  induction Y generalizing r with
  | nil => cases r <;> rfl
  | cons row Y ih =>
    cases r with
    | nil =>
      change 0 = _
      symm
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [nthN_eq]
      simp
    | cons a r =>
      change a * nthN row k + dotN r Y k = _
      rw [ih, List.length_cons, Finset.sum_range_succ', add_comm]
      rfl

theorem nthN_mulL (p d : Nat) (X Y : List (List Nat)) (i : Nat) {j : Nat} (hj : j < d) :
    nthN (nthR (mulL p d X Y) i) j = dotN (nthR X i) Y j % p := by
  induction X generalizing i with
  | nil =>
    cases i <;> rfl
  | cons r X ih =>
    cases i with
    | zero =>
      change nthN (buildL d (fun k => dotN r Y k % p) 0) j = _
      rw [nthN_eq, getD_buildL _ _ _ hj]
      rfl
    | succ i => exact ih i

theorem length_mulL (p d : Nat) (X Y : List (List Nat)) : (mulL p d X Y).length = X.length := by
  induction X with
  | nil => rfl
  | cons r X ih => exact congrArg Nat.succ ih

theorem matL_mulL {p d : Nat} {X Y : List (List Nat)} (hY : Y.length = d) :
    matL p d (mulL p d X Y) = matL p d X * matL p d Y := by
  ext i j
  simp only [matL, Matrix.of_apply, Matrix.mul_apply]
  rw [nthN_mulL p d X Y i.val j.isLt, ZMod.natCast_mod, dotN_eq, hY, Nat.cast_sum,
    ← Fin.sum_univ_eq_sum_range (fun t => ((nthN (nthR X i) t * nthN (nthR Y t) j : Nat) : ZMod p))]
  simp

theorem matL_idL (p d : Nat) : matL p d (idL d) = 1 := by
  ext i j
  simp only [matL, Matrix.of_apply, Matrix.one_apply, idL]
  rw [nthR_eq, getD_buildL _ _ _ i.isLt, nthN_eq, getD_buildL _ _ _ j.isLt]
  cases h : Nat.beq i.val j.val
  · have hne : i ≠ j := fun e => Nat.ne_of_beq_eq_false h (congrArg Fin.val e)
    simp [hne]
  · have he : i = j := Fin.ext (Nat.eq_of_beq_eq_true h)
    simp [he]

theorem length_wordL {p d : Nat} {L : Nat → List (List Nat)} (hL : ∀ c, (L c).length = d)
    (w : List Nat) : (wordL p d L w).length = d := by
  induction w with
  | nil => exact length_buildL _ _ _
  | cons c w _ => exact (length_mulL p d (L c) _).trans (hL c)

theorem matL_wordL {p d : Nat} {L : Nat → List (List Nat)} (hL : ∀ c, (L c).length = d)
    (w : List Nat) : matL p d (wordL p d L w) = (w.map fun c => matL p d (L c)).prod := by
  induction w with
  | nil => exact matL_idL p d
  | cons c w ih =>
    change matL p d (mulL p d (L c) (wordL p d L w)) = _
    rw [matL_mulL (length_wordL hL w), ih, List.map_cons, List.prod_cons]

theorem eq_of_eqN {l l' : List Nat} (h : eqN l l' = true) : l = l' := by
  induction l generalizing l' with
  | nil => cases l' <;> first | rfl | exact absurd h Bool.false_ne_true
  | cons a l ih =>
    cases l' with
    | nil => exact absurd h Bool.false_ne_true
    | cons b t =>
      change Bool.rec false (eqN l t) (Nat.beq a b) = true at h
      cases hb : Nat.beq a b
      · rw [hb] at h
        exact absurd h Bool.false_ne_true
      · rw [hb] at h
        rw [Nat.eq_of_beq_eq_true hb, ih h]

theorem eq_of_eqM {X Y : List (List Nat)} (h : eqM X Y = true) : X = Y := by
  induction X generalizing Y with
  | nil => cases Y <;> first | rfl | exact absurd h Bool.false_ne_true
  | cons r X ih =>
    cases Y with
    | nil => exact absurd h Bool.false_ne_true
    | cons s t =>
      change Bool.rec false (eqM X t) (eqN r s) = true at h
      cases hb : eqN r s
      · rw [hb] at h
        exact absurd h Bool.false_ne_true
      · rw [hb] at h
        rw [eq_of_eqN hb, ih h]

theorem matL_rows {p d : Nat} [NeZero p] (M : Matrix (Fin d) (Fin d) (ZMod p)) :
    matL p d (rowsOf M) = M := by
  ext i j
  simp [matL, rowsOf, nthN_eq, nthR_eq, List.getD_eq_getElem?_getD, ZMod.natCast_zmod_val]

theorem length_rows {p d : Nat} (M : Matrix (Fin d) (Fin d) (ZMod p)) : (rowsOf M).length = d := by
  simp [rowsOf]

end CFSG.KC.MiscCoset.Mat

end
