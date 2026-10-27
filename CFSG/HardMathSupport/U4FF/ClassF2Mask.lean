module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix

abbrev MCols := Array ℕ

@[expose] def bitF (v i : ℕ) : ZMod 2 := if v.testBit i then 1 else 0

@[expose] def MCols.toMat (A : MCols) (n m : ℕ) : Matrix (Fin n) (Fin m) (ZMod 2) :=
  Matrix.of fun i j => bitF (A.getD (j : ℕ) 0) (i : ℕ)

@[expose] def MCols.apply (A : MCols) (v : ℕ) : ℕ :=
  (List.range A.size).foldl (fun acc j => acc ^^^ (if v.testBit j then A.getD j 0 else 0)) 0

@[expose] def MCols.mul (A B : MCols) : MCols := B.map A.apply

@[expose] def MCols.add (A B : MCols) : MCols := Array.zipWith (fun a b => a ^^^ b) A B

@[expose] def MCols.one (m : ℕ) : MCols := Array.ofFn fun j : Fin m => 1 <<< (j : ℕ)

@[expose] def MCols.zero (m : ℕ) : MCols := Array.replicate m 0

@[expose] def MCols.col (v : ℕ) : MCols := #[v]

@[expose] def MCols.tabR {n m : ℕ} (M : Matrix (Fin n) (Fin m) (ZMod 2)) : MCols :=
  Array.ofFn fun y : Fin m => (List.finRange n).foldl
    (fun acc x => if M x y = 1 then acc ||| (1 <<< (x : ℕ)) else acc) 0

@[expose] def MCols.tab {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) : MCols :=
  Array.ofFn fun y : Fin n => (List.finRange n).foldl
    (fun acc x => if M x y = 1 then acc ||| (1 <<< (x : ℕ)) else acc) 0

theorem bitF_xor (a b i : ℕ) : bitF (a ^^^ b) i = bitF a i + bitF b i := by
  unfold bitF
  rw [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> decide

theorem bitF_zero (i : ℕ) : bitF 0 i = 0 := by
  simp [bitF]

theorem bitF_or_shift (acc x i : ℕ) :
    bitF (acc ||| (1 <<< x)) i = if i = x then 1 else bitF acc i := by
  by_cases h : i = x
  · subst h
    simp [bitF, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
  · have h' : x ≠ i := fun e => h e.symm
    simp [bitF, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, h, h']

theorem bitF_gate (v j i a : ℕ) :
    bitF (if v.testBit j then a else 0) i = bitF a i * bitF v j := by
  by_cases h : v.testBit j <;> simp [bitF, h]

theorem bitF_foldl_xor (g : ℕ → ℕ) (i : ℕ) (l : List ℕ) :
    ∀ acc : ℕ, bitF (l.foldl (fun acc j => acc ^^^ g j) acc) i
      = bitF acc i + (l.map fun j => bitF (g j) i).sum := by
  induction l with
  | nil => intro acc; simp
  | cons a l ih =>
    intro acc
    rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, bitF_xor]
    ring

theorem list_range_sum (f : ℕ → ZMod 2) (m : ℕ) :
    ((List.range m).map f).sum = ∑ j ∈ Finset.range m, f j := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem apply_bit_eq_sum (A : MCols) (v i : ℕ) :
    bitF (A.apply v) i = ∑ j ∈ Finset.range A.size, bitF (A.getD j 0) i * bitF v j := by
  unfold MCols.apply
  rw [bitF_foldl_xor, bitF_zero, zero_add, list_range_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact bitF_gate v j i (A.getD j 0)

theorem toMat_apply_bit (A : MCols) (n m : ℕ) (hA : A.size = m) (v : ℕ) (i : Fin n) :
    bitF (A.apply v) (i : ℕ) = ∑ j : Fin m, A.toMat n m i j * bitF v (j : ℕ) := by
  rw [apply_bit_eq_sum, hA, Finset.sum_range]
  rfl

theorem toMat_apply (A : MCols) (n m : ℕ) (hA : A.size = m) (v : ℕ) :
    (fun i : Fin n => bitF (A.apply v) (i : ℕ)) =
      A.toMat n m *ᵥ (fun j : Fin m => bitF v (j : ℕ)) := by
  funext i
  exact toMat_apply_bit A n m hA v i

theorem size_mul (A B : MCols) : (A.mul B).size = B.size := by
  simp [MCols.mul]

theorem getD_mul (A B : MCols) (j : ℕ) (hj : j < B.size) :
    (A.mul B).getD j 0 = A.apply (B.getD j 0) := by
  simp [MCols.mul, Array.getD_eq_getD_getElem?, hj]

theorem toMat_mul (A B : MCols) (n m k : ℕ) (hA : A.size = m) (hB : B.size = k) :
    (A.mul B).toMat n k = A.toMat n m * B.toMat m k := by
  ext i j
  have hj : (j : ℕ) < B.size := by rw [hB]; exact j.isLt
  have h1 : (A.mul B).toMat n k i j = bitF (A.apply (B.getD (j : ℕ) 0)) (i : ℕ) := by
    rw [← getD_mul A B j hj]
    rfl
  rw [h1, Matrix.mul_apply, toMat_apply_bit A n m hA]
  rfl

theorem size_add (A B : MCols) (h : B.size = A.size) : (A.add B).size = A.size := by
  simp [MCols.add, h]

theorem getD_add (A B : MCols) (j : ℕ) (hA : j < A.size) (hB : j < B.size) :
    (A.add B).getD j 0 = A.getD j 0 ^^^ B.getD j 0 := by
  have hj : j < (A.add B).size := by
    simp only [MCols.add, Array.size_zipWith]
    omega
  simp [MCols.add, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem, hA, hB, hj]

theorem toMat_add (A B : MCols) (n m : ℕ) (hA : A.size = m) (hB : B.size = m) :
    (A.add B).toMat n m = A.toMat n m + B.toMat n m := by
  ext i j
  have hj : (j : ℕ) < m := j.isLt
  have h1 : (A.add B).toMat n m i j
      = bitF (A.getD (j : ℕ) 0 ^^^ B.getD (j : ℕ) 0) (i : ℕ) := by
    rw [← getD_add A B j (by rw [hA]; exact hj) (by rw [hB]; exact hj)]
    rfl
  rw [h1, bitF_xor, Matrix.add_apply]
  rfl

theorem size_one (m : ℕ) : (MCols.one m).size = m := by
  simp [MCols.one]

theorem getD_one (m j : ℕ) (hj : j < m) : (MCols.one m).getD j 0 = 1 <<< j := by
  simp [MCols.one, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hj]

theorem toMat_one (m : ℕ) : (MCols.one m).toMat m m = 1 := by
  ext i j
  have h1 : (MCols.one m).toMat m m i j = bitF (1 <<< (j : ℕ)) (i : ℕ) := by
    rw [← getD_one m j j.isLt]
    rfl
  rw [h1, Matrix.one_apply]
  unfold bitF
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : i = j
  · subst h
    simp
  · have h' : (j : ℕ) ≠ (i : ℕ) := fun e => h (Fin.ext e).symm
    simp [h, h']

theorem size_zero (m : ℕ) : (MCols.zero m).size = m := by
  simp [MCols.zero]

theorem toMat_zero (n m : ℕ) : (MCols.zero m).toMat n m = 0 := by
  ext i j
  have hj : (j : ℕ) < m := j.isLt
  have h2 : (MCols.zero m).getD (j : ℕ) 0 = 0 := by
    simp [MCols.zero, Array.getD_eq_getD_getElem?, hj]
  rw [Matrix.zero_apply]
  show bitF ((MCols.zero m).getD (j : ℕ) 0) (i : ℕ) = 0
  rw [h2, bitF_zero]

theorem size_col (v : ℕ) : (MCols.col v).size = 1 := rfl

theorem toMat_col (v n : ℕ) :
    (MCols.col v).toMat n 1 = Matrix.of fun (i : Fin n) (_ : Fin 1) => bitF v (i : ℕ) := by
  ext i j
  have hj : (j : ℕ) = 0 := by
    have := j.isLt
    omega
  show bitF ((MCols.col v).getD (j : ℕ) 0) (i : ℕ) = bitF v (i : ℕ)
  rw [hj]
  rfl

theorem bitF_foldl_tab {n m : ℕ} (M : Matrix (Fin n) (Fin m) (ZMod 2)) (y : Fin m) (i : Fin n) :
    ∀ (L : List (Fin n)) (acc : ℕ),
      bitF (L.foldl (fun acc x => if M x y = 1 then acc ||| (1 <<< (x : ℕ)) else acc) acc)
          (i : ℕ)
        = if i ∈ L ∧ M i y = 1 then 1 else bitF acc (i : ℕ) := by
  intro L
  induction L with
  | nil => intro acc; simp
  | cons x L ih =>
    intro acc
    rw [List.foldl_cons, ih]
    by_cases hi : i = x
    · subst hi
      by_cases hP : M i y = 1
      · simp [hP, bitF_or_shift]
      · simp [hP]
    · by_cases hx : M x y = 1
      · simp [hx, hi, bitF_or_shift, Fin.val_inj]
      · simp [hx, hi]

theorem zmod2_ite_self (z : ZMod 2) : (if z = 1 then 1 else 0) = z := by
  revert z
  decide

theorem getD_tabR {n m : ℕ} (M : Matrix (Fin n) (Fin m) (ZMod 2)) (j : Fin m) :
    (MCols.tabR M).getD (j : ℕ) 0 = (List.finRange n).foldl
      (fun acc x => if M x j = 1 then acc ||| (1 <<< (x : ℕ)) else acc) 0 := by
  have hj : (j : ℕ) < m := j.isLt
  simp [MCols.tabR, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem, hj]

theorem toMat_tabR {n m : ℕ} (M : Matrix (Fin n) (Fin m) (ZMod 2)) :
    (MCols.tabR M).toMat n m = M := by
  ext i j
  show bitF ((MCols.tabR M).getD (j : ℕ) 0) (i : ℕ) = M i j
  rw [getD_tabR M j, bitF_foldl_tab M j i (List.finRange n) 0, bitF_zero]
  simp only [List.mem_finRange, true_and]
  exact zmod2_ite_self (M i j)

theorem tab_eq_tabR {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) :
    MCols.tab M = MCols.tabR M := rfl

theorem tab_size {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) : (MCols.tab M).size = n := by
  simp [MCols.tab]

theorem toMat_tab {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) :
    (MCols.tab M).toMat n n = M :=
  toMat_tabR M

end CFSG.HardMathSupport.U4FF
