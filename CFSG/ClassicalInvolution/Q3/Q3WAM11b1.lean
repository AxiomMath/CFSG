module

public import CFSG.ClassicalInvolution.Q3.M11Exact

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Blueprint CFSG.Sporadic.Mathieu Equiv

@[expose] def M11InvAdj (a b : ↥NativeSporadic.M11) : Prop :=
  orderOf a = 2 ∧ orderOf b = 2 ∧ a ≠ b ∧ a * b = b * a

section Lists

private def pl (p : Perm (Fin 11)) : List ℕ := (List.finRange 11).map fun i => (p i).val

private theorem pl_getD (p : Perm (Fin 11)) (j : Fin 11) : (pl p).getD j.val 0 = (p j).val := by
  simp [pl, List.getD_eq_getElem?_getD]

private theorem pl_injective : Function.Injective pl := by
  intro p q h
  ext i
  have h1 := pl_getD p i
  have h2 := pl_getD q i
  rw [h] at h1
  exact h1.symm.trans h2

private def lcomp (a b : List ℕ) : List ℕ := b.map fun j => a.getD j 0

private theorem pl_mul (p q : Perm (Fin 11)) : pl (p * q) = lcomp (pl p) (pl q) := by
  have hq : pl q = (List.finRange 11).map fun i => (q i).val := rfl
  have h : lcomp (pl p) (pl q) = (List.finRange 11).map fun i => (pl p).getD (q i).val 0 := by
    unfold lcomp
    rw [hq, List.map_map]
    rfl
  rw [h]
  have hpq : pl (p * q) = (List.finRange 11).map fun i => ((p * q) i).val := rfl
  rw [hpq]
  apply List.map_congr_left
  intro i _
  rw [pl_getD]
  rfl

private theorem pl_one : pl (1 : Perm (Fin 11)) = List.range 11 := by decide +kernel

private def lLetter : ℕ → List ℕ
  | 0 => [0, 9, 2, 10, 6, 5, 4, 8, 7, 1, 3]
  | 1 => [3, 4, 7, 2, 5, 8, 6, 0, 1, 9, 10]
  | 2 => [0, 9, 2, 10, 6, 5, 4, 8, 7, 1, 3]
  | _ => [7, 8, 3, 0, 1, 4, 6, 2, 5, 9, 10]

private theorem pl_letter (g : ℕ) : pl (m11Letter g) = lLetter g := by
  match g with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | 2 => decide +kernel
  | _ + 3 =>
    have h : pl m11gB⁻¹ = lLetter 3 := by decide +kernel
    exact h

private def lprod : List ℕ → List ℕ
  | [] => List.range 11
  | g :: w => lcomp (lLetter g) (lprod w)

private theorem pl_eval (w : List ℕ) : pl (m11Eval w) = lprod w := by
  induction w with
  | nil => rw [show m11Eval [] = 1 from rfl, pl_one]; rfl
  | cons g w ih => rw [show m11Eval (g :: w) = m11Letter g * m11Eval w from rfl, pl_mul,
      pl_letter, ih]; rfl

private def flipL : ℕ → ℕ
  | 0 => 2
  | 1 => 3
  | 2 => 0
  | _ => 1

private def invWord (w : List ℕ) : List ℕ := (w.map flipL).reverse

private theorem m11Eval_append (u v : List ℕ) : m11Eval (u ++ v) = m11Eval u * m11Eval v := by
  induction u with
  | nil => simp [m11Eval]
  | cons g u ih => simp [m11Eval, ih, mul_assoc]

private theorem m11Letter_flip (g : ℕ) : m11Letter (flipL g) = (m11Letter g)⁻¹ := by
  match g with
  | 0 => rfl
  | 1 => rfl
  | 2 => exact (inv_inv _).symm
  | _ + 3 => exact (inv_inv _).symm

private theorem m11Eval_invWord (w : List ℕ) : m11Eval (invWord w) = (m11Eval w)⁻¹ := by
  induction w with
  | nil => simp [invWord, m11Eval]
  | cons g w ih =>
    have h1 : invWord (g :: w) = invWord w ++ [flipL g] := by simp [invWord]
    rw [h1, m11Eval_append, ih, show m11Eval (g :: w) = m11Letter g * m11Eval w from rfl,
      mul_inv_rev]
    simp [m11Eval, m11Letter_flip]

end Lists

section Data

private def m11bWords : List (List ℕ) :=
  [[], [1, 1], [1, 0, 3], [0, 1, 1, 0], [1, 1, 0, 1], [1, 0, 1, 1, 0], [0, 3, 0, 3, 0], [0, 3, 0,
    3, 0, 3], [1, 0, 1, 0, 3, 0, 3], [0, 1, 0, 3, 0, 1, 1, 0], [0, 1, 0, 1, 1, 0, 3, 0], [3, 0, 1,
    1, 0, 3, 0, 3, 0], [3, 0, 3, 0, 1, 1, 0, 3, 0, 3, 0], [0, 1], [3, 0, 3], [3, 0, 1, 1, 0], [0,
    1, 1, 0, 1], [1, 1, 0, 3, 0, 3, 0], [0, 1, 1, 0, 1, 0, 1], [3, 0, 1, 0, 3, 0, 3], [0, 1, 0, 3,
    0, 1, 0, 1], [1, 0, 1, 1, 0, 3, 0, 3, 0], [0, 1, 1, 0, 3, 0, 3, 0, 3, 0], [3, 0], [1, 0, 1],
    [1, 0, 1, 0, 1], [3, 0, 3, 0, 3], [0, 3, 0, 1, 0, 1], [1, 1, 0, 3, 0, 3], [1, 0, 3, 0, 1, 1,
    0], [1, 0, 3, 0, 3, 0, 3, 0], [0, 1, 1, 0, 3, 0, 3, 0, 1], [3, 0, 3, 0, 1, 0, 3, 0, 3], [3],
    [1, 1, 0], [1, 0, 3, 0], [0, 1, 0, 3, 0, 3], [0, 1, 1, 0, 1, 0, 3], [0, 3, 0, 1, 1, 0, 3, 0],
    [0, 1, 0, 1, 0, 1, 0, 3], [0, 3, 0, 3, 0, 3, 0, 3, 0], [3, 0, 1, 1, 0, 1, 0, 1, 0, 1], [3, 0,
    1, 1, 0, 3, 0, 3, 0, 1], [0, 1, 1], [1, 1, 0, 3, 0, 1], [1, 0, 1, 0, 1, 0, 1], [1, 0, 3, 0, 1,
    0, 1], [1, 0, 1, 0, 1, 0, 3], [1, 1, 0, 1, 0, 3, 0, 3, 0], [0, 1, 1, 0, 1, 0, 3, 0, 3], [0, 1,
    1, 0, 1, 1, 0, 1, 0, 3], [1], [1, 1, 0, 3, 0], [0, 3, 0, 1, 0, 1, 0, 1], [3, 0, 1, 1, 0, 3, 0,
    1], [1, 0, 1, 1, 0, 1, 0, 3], [3, 0, 1, 0, 1, 0, 1, 0, 1], [0, 1, 1, 0, 1, 0, 1, 0, 1], [1, 0,
    1, 0, 1, 0, 1, 0, 3], [1, 1, 0, 1, 0, 1], [0, 3, 0, 1, 0, 3], [0, 3, 0, 1, 0, 1, 1, 0], [0, 1,
    1, 0, 3, 0, 3, 0], [0, 3, 0, 3, 0, 1, 0, 3], [1, 0, 3, 0, 1, 0, 1, 1, 0], [3, 0, 1, 0, 1, 0,
    3, 0, 1], [1, 0, 1, 0, 3, 0, 1, 0, 1, 1, 0], [0, 1, 0, 3], [0, 3, 0, 3, 0, 1], [1, 1, 0, 1, 0,
    3], [1, 0, 3, 0, 3, 0, 3], [1, 1, 0, 3, 0, 3, 0, 1], [0, 3, 0, 1, 0, 3, 0, 3], [0, 1, 1, 0, 3,
    0, 1, 0, 3], [1, 0, 3, 0, 3, 0, 1, 0, 3], [0, 1, 0, 1, 0, 1, 0, 1, 0, 1], [3, 0, 3, 0, 1, 1,
    0, 1, 0, 1], [1, 0, 3, 0, 3], [0, 1, 0, 1, 0, 1], [1, 0, 1, 0, 3, 0, 1], [0, 1, 0, 1, 0, 1, 0,
    1], [3, 0, 3, 0, 1, 0, 1, 1, 0], [3, 0, 1, 0, 3, 0, 1, 1, 0], [1, 1, 0, 3, 0, 3, 0, 3, 0], [3,
    0, 1, 0, 1, 1, 0, 3, 0, 1], [0, 3, 0, 3], [3, 0, 3, 0, 1, 0, 3], [1, 0, 1, 0, 3, 0, 3, 0], [1,
    1, 0, 1, 0, 3, 0, 3], [1, 0, 1, 0, 1, 0, 1, 0, 1], [3, 0, 3, 0, 1, 0, 3, 0, 1], [1, 1, 0, 3,
    0, 1, 0, 1, 1, 0], [3, 0, 3, 0, 1, 1, 0, 1, 0, 3], [1, 0, 1, 0, 3], [1, 1, 0, 1, 0, 1, 0, 1],
    [1, 1, 0, 3, 0, 1, 0, 1], [1, 0, 1, 1, 0, 3, 0, 1], [1, 1, 0, 3, 0, 1, 0, 3], [0, 1, 0, 1, 0,
    3, 0, 3, 0], [1, 1, 0, 1, 1, 0, 1, 0, 3], [0, 1, 0, 1, 0, 1, 0, 1, 0, 3], [1, 0, 3, 0, 1], [3,
    0, 3, 0, 3, 0], [0, 3, 0, 1, 1, 0, 1, 0, 1], [1, 1, 0, 1, 0, 1, 0, 3, 0, 1], [1, 1, 0, 3, 0,
    1, 0, 3, 0, 1], [0, 3, 0, 1, 1, 0, 1, 0, 1, 0, 1], [1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1], [1, 1,
    0, 1, 0, 1, 1, 0, 3, 0, 1], [3, 0, 1, 0, 3], [3, 0, 1, 0, 3, 0, 1], [3, 0, 3, 0, 3, 0, 3, 0],
    [1, 0, 1, 0, 1, 0, 3, 0, 1], [1, 0, 3, 0, 1, 0, 3, 0, 1], [0, 1, 0, 1, 1, 0, 3, 0, 3, 0], [0,
    1, 0, 1, 0, 1, 0, 3, 0, 1], [0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0], [0, 3], [0, 3, 0, 1], [0, 1, 0,
    1, 1, 0], [0, 1, 0, 3, 0, 3, 0], [3, 0, 1, 0, 1, 0, 1], [3, 0, 3, 0, 1, 0, 1], [1, 0], [3, 0,
    1], [3, 0, 1, 0, 1], [1, 0, 1, 0, 1, 1, 0, 3, 0, 3, 0], [0, 3, 0], [3, 0, 1, 1, 0, 1, 0, 3],
    [0], [3, 0, 3, 0], [0, 1, 1, 0, 3, 0, 1], [0, 1, 1, 0, 1, 0, 3, 0, 3, 0], [0, 1, 0, 1], [1, 1,
    0, 1, 1, 0, 3, 0, 3, 0], [0, 3, 0, 3, 0, 3, 0], [1, 0, 1, 0, 1, 1, 0, 3, 0, 1], [1, 0, 3, 0,
    1, 0, 3], [3, 0, 1, 0, 3, 0, 3, 0], [3, 0, 3, 0, 1], [1, 0, 3, 0, 3, 0], [0, 1, 0, 1, 0, 3, 0,
    1], [0, 3, 0, 1, 0, 3, 0, 1], [0, 1, 0, 1, 1, 0, 3, 0, 1], [0, 3, 0, 3, 0, 1, 1, 0, 3, 0, 3,
    0], [0, 3, 0, 1, 1, 0], [0, 1, 1, 0, 3, 0], [3, 0, 1, 0, 1, 1, 0], [0, 1, 0, 1, 0, 3, 0, 1, 0,
    1, 1, 0], [0, 1, 0, 1, 0, 3], [1, 0, 1, 0, 1, 0, 3, 0, 3, 0], [0, 1, 0, 3, 0, 1], [3, 0, 3, 0,
    3, 0, 1], [1, 1, 0, 1, 0, 3, 0, 1], [1, 0, 1, 1, 0, 3, 0, 3, 0, 3, 0], [0, 1, 1, 0, 3, 0, 3],
    [3, 0, 1, 1, 0, 3, 0], [1, 0, 1, 1, 0, 3, 0], [0, 1, 0, 3, 0, 1, 0, 1, 1, 0], [3, 0, 3, 0, 1,
    1, 0, 1, 0, 1, 0, 1], [1, 0, 3, 0, 3, 0, 1], [3, 0, 1, 1, 0, 1, 0, 1], [0, 3, 0, 1, 1, 0, 1,
    0, 3], [1, 1, 0, 1, 1, 0, 3, 0], [0, 3, 0, 1, 1, 0, 3, 0, 3, 0]]

private def m11bLists : List (List ℕ) :=
  [[0, 5, 7, 3, 9, 1, 6, 2, 10, 4, 8], [3, 5, 2, 0, 10, 1, 6, 7, 9, 8, 4], [6, 1, 8, 3, 9, 5, 0,
    10, 2, 4, 7], [6, 9, 2, 3, 5, 4, 0, 7, 10, 1, 8], [0, 5, 4, 6, 2, 1, 3, 9, 8, 7, 10], [0, 10,
    2, 6, 9, 8, 3, 7, 5, 4, 1], [0, 1, 9, 6, 7, 5, 3, 4, 10, 2, 8], [3, 1, 7, 0, 8, 5, 6, 2, 4,
    10, 9], [0, 8, 7, 6, 4, 10, 3, 2, 1, 9, 5], [6, 4, 7, 3, 1, 9, 0, 2, 8, 5, 10], [3, 2, 1, 0,
    4, 7, 6, 5, 10, 9, 8], [6, 5, 10, 3, 4, 1, 0, 8, 7, 9, 2], [3, 7, 5, 0, 9, 2, 6, 1, 8, 4, 10],
    [8, 5, 2, 9, 4, 1, 7, 6, 0, 3, 10], [4, 1, 6, 10, 0, 5, 2, 7, 9, 8, 3], [0, 4, 2, 3, 1, 10, 7,
    6, 9, 8, 5], [0, 8, 6, 3, 10, 9, 2, 7, 1, 5, 4], [9, 1, 2, 8, 10, 5, 7, 6, 3, 0, 4], [5, 3, 7,
    1, 10, 0, 6, 2, 8, 9, 4], [3, 10, 2, 0, 5, 4, 7, 6, 8, 9, 1], [3, 9, 6, 0, 4, 8, 2, 7, 5, 1,
    10], [10, 5, 6, 4, 3, 1, 2, 7, 8, 9, 0], [1, 0, 7, 5, 4, 3, 6, 2, 9, 8, 10], [2, 1, 0, 5, 9,
    3, 8, 7, 6, 4, 10], [6, 3, 9, 1, 8, 5, 0, 7, 4, 2, 10], [6, 1, 2, 5, 7, 3, 0, 4, 8, 10, 9],
    [10, 3, 8, 1, 4, 5, 7, 6, 2, 9, 0], [0, 3, 4, 1, 2, 5, 6, 10, 9, 8, 7], [8, 1, 6, 5, 4, 3, 2,
    10, 0, 9, 7], [4, 5, 8, 3, 0, 1, 9, 7, 2, 6, 10], [0, 1, 8, 5, 10, 3, 6, 9, 2, 7, 4], [7, 3,
    2, 1, 9, 5, 10, 0, 8, 4, 6], [9, 5, 2, 3, 6, 1, 4, 10, 8, 0, 7], [0, 9, 3, 2, 8, 10, 6, 7, 4,
    1, 5], [4, 9, 2, 7, 0, 6, 5, 3, 8, 1, 10], [5, 1, 2, 7, 6, 0, 4, 3, 10, 9, 8], [6, 1, 3, 2,
    10, 8, 0, 7, 5, 9, 4], [10, 1, 7, 3, 5, 4, 8, 2, 6, 9, 0], [1, 0, 3, 2, 4, 5, 9, 7, 10, 6, 8],
    [0, 8, 2, 7, 5, 4, 6, 3, 1, 10, 9], [6, 10, 2, 7, 4, 5, 0, 3, 9, 8, 1], [9, 6, 3, 2, 5, 4, 1,
    7, 8, 0, 10], [8, 9, 7, 3, 4, 5, 10, 2, 0, 1, 6], [10, 7, 2, 6, 4, 9, 3, 1, 8, 5, 0], [8, 4,
    5, 6, 1, 2, 3, 7, 0, 9, 10], [0, 6, 4, 5, 2, 3, 1, 7, 10, 9, 8], [10, 9, 4, 3, 2, 7, 6, 5, 8,
    1, 0], [0, 3, 2, 1, 4, 6, 5, 9, 10, 7, 8], [8, 2, 1, 3, 5, 4, 6, 9, 0, 7, 10], [8, 1, 4, 7, 2,
    5, 9, 3, 0, 6, 10], [10, 1, 3, 2, 6, 5, 4, 9, 8, 7, 0], [7, 10, 2, 3, 8, 9, 6, 0, 4, 5, 1],
    [2, 10, 0, 8, 4, 6, 5, 7, 3, 9, 1], [7, 1, 2, 6, 5, 4, 3, 0, 9, 8, 10], [0, 10, 7, 4, 3, 5, 9,
    2, 8, 6, 1], [7, 6, 2, 10, 4, 8, 1, 0, 5, 9, 3], [2, 9, 0, 6, 10, 5, 3, 7, 8, 1, 4], [0, 1, 7,
    9, 6, 8, 4, 2, 5, 3, 10], [2, 4, 0, 3, 1, 8, 6, 7, 5, 10, 9], [5, 1, 8, 6, 4, 0, 3, 7, 2, 10,
    9], [5, 1, 10, 3, 7, 0, 6, 4, 9, 8, 2], [1, 0, 6, 9, 7, 5, 2, 4, 8, 3, 10], [1, 0, 2, 6, 8, 5,
    3, 10, 4, 9, 7], [0, 5, 9, 10, 4, 1, 8, 7, 6, 2, 3], [5, 1, 9, 4, 3, 0, 7, 6, 8, 2, 10], [1,
    0, 9, 3, 10, 5, 6, 8, 7, 2, 4], [0, 5, 2, 8, 7, 1, 10, 4, 3, 9, 6], [4, 6, 7, 8, 0, 5, 1, 2,
    3, 9, 10], [0, 1, 4, 3, 2, 6, 5, 8, 7, 10, 9], [3, 1, 8, 0, 7, 6, 5, 4, 2, 9, 10], [7, 5, 3,
    2, 4, 1, 6, 0, 8, 10, 9], [8, 6, 2, 4, 3, 5, 1, 7, 0, 10, 9], [10, 1, 2, 9, 8, 6, 5, 7, 4, 3,
    0], [3, 6, 9, 0, 4, 5, 1, 10, 8, 2, 7], [0, 6, 10, 3, 8, 5, 1, 9, 4, 7, 2], [2, 5, 0, 7, 8, 1,
    6, 3, 4, 9, 10], [9, 1, 7, 10, 4, 6, 5, 2, 8, 0, 3], [4, 1, 10, 6, 0, 7, 3, 5, 8, 9, 2], [4,
    3, 2, 1, 0, 10, 8, 7, 6, 9, 5], [9, 8, 2, 5, 4, 3, 10, 7, 1, 0, 6], [0, 1, 6, 7, 9, 10, 2, 3,
    8, 4, 5], [9, 2, 1, 6, 4, 5, 3, 8, 7, 0, 10], [0, 8, 3, 2, 9, 5, 7, 6, 1, 4, 10], [9, 7, 8, 3,
    4, 10, 6, 1, 2, 0, 5], [4, 8, 5, 3, 0, 2, 6, 10, 1, 9, 7], [6, 7, 4, 10, 2, 5, 0, 1, 8, 9, 3],
    [0, 2, 1, 10, 7, 9, 6, 4, 8, 5, 3], [0, 4, 9, 8, 1, 7, 6, 5, 3, 2, 10], [7, 4, 6, 3, 1, 5, 2,
    0, 10, 9, 8], [2, 1, 0, 3, 4, 9, 7, 6, 10, 5, 8], [1, 0, 2, 8, 6, 9, 4, 7, 3, 5, 10], [6, 1,
    5, 8, 4, 2, 0, 9, 3, 7, 10], [5, 4, 2, 10, 1, 0, 9, 7, 8, 6, 3], [7, 2, 1, 5, 6, 3, 4, 0, 8,
    9, 10], [0, 10, 8, 3, 6, 7, 4, 5, 2, 9, 1], [8, 1, 2, 10, 9, 7, 6, 5, 0, 4, 3], [3, 1, 2, 0,
    4, 10, 9, 8, 7, 6, 5], [10, 2, 1, 8, 9, 5, 6, 7, 3, 4, 0], [0, 2, 1, 3, 4, 8, 9, 10, 5, 6, 7],
    [3, 8, 10, 0, 6, 5, 4, 7, 1, 9, 2], [2, 3, 0, 1, 4, 7, 9, 5, 8, 6, 10], [6, 8, 2, 4, 3, 7, 0,
    5, 1, 9, 10], [6, 2, 1, 9, 4, 10, 0, 7, 8, 3, 5], [7, 1, 10, 9, 4, 5, 8, 0, 6, 3, 2], [0, 10,
    5, 9, 4, 2, 6, 8, 7, 3, 1], [5, 6, 2, 3, 9, 0, 1, 8, 7, 4, 10], [1, 0, 10, 3, 9, 6, 5, 7, 8,
    4, 2], [2, 1, 0, 4, 3, 5, 10, 8, 7, 9, 6], [0, 7, 10, 4, 3, 8, 6, 1, 5, 9, 2], [5, 7, 3, 2, 4,
    0, 8, 1, 6, 9, 10], [0, 7, 9, 3, 5, 4, 10, 1, 8, 2, 6], [4, 7, 2, 9, 0, 5, 6, 1, 10, 3, 8],
    [9, 1, 5, 4, 3, 2, 6, 7, 10, 0, 8], [0, 9, 5, 3, 7, 2, 8, 4, 6, 1, 10], [3, 1, 4, 0, 2, 9, 10,
    7, 8, 5, 6], [1, 0, 5, 7, 4, 2, 10, 3, 8, 9, 6], [3, 4, 2, 0, 1, 5, 8, 9, 6, 7, 10], [0, 9,
    10, 5, 4, 3, 7, 6, 8, 1, 2], [1, 0, 4, 3, 2, 8, 7, 6, 5, 9, 10], [0, 6, 2, 9, 10, 7, 1, 5, 8,
    3, 4], [5, 8, 4, 9, 2, 0, 6, 7, 1, 3, 10], [8, 7, 2, 3, 10, 6, 5, 1, 0, 9, 4], [8, 3, 10, 1,
    4, 9, 6, 7, 0, 5, 2], [2, 7, 0, 3, 6, 5, 4, 1, 9, 8, 10], [9, 1, 6, 3, 8, 7, 2, 5, 4, 0, 10],
    [0, 7, 6, 8, 4, 5, 2, 1, 3, 10, 9], [0, 1, 3, 2, 4, 7, 10, 5, 9, 8, 6], [2, 6, 0, 3, 7, 10, 1,
    4, 8, 9, 5], [0, 4, 3, 2, 1, 6, 5, 10, 8, 9, 7], [0, 6, 8, 7, 4, 9, 1, 3, 2, 5, 10], [0, 2, 1,
    7, 10, 5, 8, 3, 6, 9, 4], [7, 1, 5, 3, 10, 2, 9, 0, 8, 6, 4], [7, 8, 9, 3, 4, 6, 5, 0, 1, 2,
    10], [4, 2, 1, 3, 0, 5, 7, 6, 8, 10, 9], [0, 1, 5, 10, 8, 2, 7, 6, 4, 9, 3], [4, 10, 9, 5, 0,
    3, 6, 7, 8, 2, 1], [1, 0, 8, 10, 5, 4, 6, 7, 2, 9, 3], [5, 9, 2, 8, 4, 0, 6, 10, 3, 1, 7], [9,
    3, 2, 1, 7, 8, 6, 4, 5, 0, 10], [0, 3, 6, 1, 5, 4, 2, 8, 7, 9, 10], [5, 10, 6, 3, 4, 0, 2, 9,
    8, 7, 1], [1, 0, 2, 4, 3, 10, 6, 9, 8, 7, 5], [0, 2, 1, 4, 3, 6, 5, 7, 9, 8, 10], [10, 4, 2,
    5, 1, 3, 6, 8, 7, 9, 0], [10, 6, 5, 3, 4, 2, 1, 7, 9, 8, 0], [0, 7, 2, 5, 8, 3, 9, 1, 4, 6,
    10], [2, 1, 0, 9, 5, 4, 6, 10, 8, 3, 7], [9, 10, 4, 3, 2, 5, 8, 7, 6, 0, 1], [0, 1, 2, 4, 3,
    9, 8, 10, 6, 5, 7], [8, 1, 9, 3, 6, 10, 4, 7, 0, 2, 5], [10, 8, 2, 3, 7, 5, 9, 4, 1, 6, 0],
    [4, 1, 2, 3, 0, 8, 10, 9, 5, 7, 6], [0, 3, 5, 1, 6, 2, 4, 7, 8, 10, 9], [0, 4, 8, 9, 1, 5, 10,
    7, 2, 3, 6], [7, 9, 8, 4, 3, 5, 6, 0, 2, 1, 10], [7, 1, 4, 8, 2, 10, 6, 0, 3, 9, 5], [9, 4,
    10, 7, 1, 5, 6, 3, 8, 0, 2], [10, 1, 9, 7, 4, 8, 6, 3, 5, 2, 0], [5, 2, 1, 3, 8, 0, 10, 7, 4,
    9, 6], [0, 9, 2, 10, 6, 5, 4, 8, 7, 1, 3], [1, 0, 2, 3, 4, 7, 8, 5, 6, 10, 9], [8, 10, 3, 2,
    7, 5, 6, 4, 0, 9, 1], [0, 1, 10, 8, 5, 4, 9, 7, 3, 6, 2], [2, 8, 0, 10, 4, 5, 6, 9, 1, 7, 3],
    [4, 1, 3, 2, 0, 9, 6, 8, 7, 5, 10]]

private def m11bPar : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6,
    6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9,
    10, 10, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 11, 11, 12, 12, 12, 12, 12, 12, 12,
    12, 13, 13, 13, 13, 13, 13, 14, 14, 14, 14, 15, 15, 16, 16, 16, 16, 17, 17, 19, 19, 20, 20,
    21, 21, 21, 21, 21, 21, 23, 23, 23, 23, 24, 25, 31, 31, 31, 31, 33, 34, 35, 35, 35, 38, 38,
    38, 39, 41]

private def m11bTable : List (List ℕ) :=
  [[129, 51, 129, 33], [43, 33, 43, 51], [67, 43, 67, 117], [34, 5, 34, 15], [16, 124, 16, 24],
    [119, 16, 119, 3], [130, 140, 130, 102], [26, 70, 26, 70], [30, 88, 30, 36], [29, 53, 29, 82],
    [157, 161, 157, 155], [164, 62, 164, 134], [144, 164, 144, 154], [51, 24, 51, 124], [85, 117,
    85, 43], [145, 3, 145, 16], [4, 15, 4, 5], [62, 102, 62, 140], [59, 155, 59, 161], [72, 36,
    72, 88], [46, 82, 46, 53], [114, 134, 114, 62], [83, 154, 83, 164], [127, 129, 127, 34], [133,
    4, 133, 13], [78, 59, 78, 133], [7, 85, 7, 28], [125, 46, 125, 122], [155, 26, 155, 77], [9,
    145, 9, 145], [8, 83, 8, 135], [71, 114, 71, 42], [90, 72, 90, 74], [117, 0, 117, 1], [3, 23,
    3, 123], [35, 52, 35, 127], [77, 8, 77, 19], [69, 55, 69, 128], [156, 54, 156, 96], [47, 58,
    47, 58], [111, 56, 111, 89], [106, 57, 106, 116], [154, 31, 154, 126], [1, 14, 1, 2], [131,
    139, 131, 101], [80, 94, 80, 78], [20, 95, 20, 27], [39, 147, 39, 149], [132, 138, 132, 87],
    [88, 100, 88, 100], [99, 76, 99, 73], [13, 1, 13, 0], [146, 130, 146, 35], [121, 20, 121, 9],
    [153, 131, 153, 38], [95, 99, 95, 37], [56, 80, 56, 40], [94, 132, 94, 41], [100, 39, 100,
    39], [18, 125, 18, 25], [109, 137, 109, 86], [147, 64, 147, 81], [17, 21, 17, 11], [86, 74,
    86, 72], [158, 91, 158, 61], [81, 141, 81, 104], [148, 158, 148, 158], [2, 93, 2, 109], [139,
    160, 139, 152], [37, 109, 37, 93], [122, 7, 122, 7], [31, 152, 31, 160], [19, 63, 19, 32],
    [97, 50, 97, 103], [82, 32, 82, 63], [89, 75, 89, 75], [136, 103, 136, 50], [36, 28, 36, 85],
    [25, 45, 25, 121], [141, 153, 141, 151], [45, 89, 45, 56], [65, 61, 65, 91], [74, 9, 74, 20],
    [22, 111, 22, 30], [91, 143, 91, 108], [14, 77, 14, 26], [63, 60, 63, 97], [98, 48, 98, 120],
    [49, 19, 49, 8], [75, 40, 75, 80], [32, 142, 32, 105], [84, 81, 84, 64], [92, 162, 92, 150],
    [149, 69, 149, 67], [57, 121, 57, 45], [55, 122, 55, 46], [143, 38, 143, 131], [73, 86, 73,
    137], [87, 150, 87, 162], [50, 128, 50, 55], [58, 49, 58, 49], [151, 44, 151, 118], [135, 6,
    135, 17], [161, 73, 161, 76], [104, 65, 104, 112], [105, 90, 105, 113], [41, 148, 41, 159],
    [107, 115, 107, 115], [126, 84, 126, 136], [60, 67, 60, 69], [142, 151, 142, 153], [40, 135,
    40, 83], [115, 104, 115, 141], [113, 105, 113, 142], [21, 126, 21, 31], [112, 107, 112, 107],
    [150, 41, 150, 132], [33, 2, 33, 14], [124, 101, 124, 139], [5, 149, 5, 147], [140, 87, 140,
    138], [53, 78, 53, 94], [70, 27, 70, 95], [123, 34, 123, 129], [118, 13, 118, 4], [27, 133,
    27, 59], [108, 42, 108, 114], [23, 35, 23, 130], [162, 37, 162, 99], [0, 123, 0, 23], [6, 127,
    6, 52], [44, 96, 44, 54], [48, 116, 48, 57], [24, 25, 24, 125], [134, 11, 134, 21], [102, 30,
    102, 111], [76, 108, 76, 143], [137, 97, 137, 60], [160, 120, 160, 48], [68, 118, 68, 44],
    [120, 17, 120, 6], [79, 112, 79, 65], [110, 113, 110, 90], [96, 136, 96, 84], [12, 159, 12,
    148], [15, 29, 15, 29], [52, 157, 52, 156], [61, 119, 61, 47], [66, 144, 66, 106], [93, 47,
    93, 119], [116, 92, 116, 98], [101, 79, 101, 110], [152, 68, 152, 71], [54, 110, 54, 79], [42,
    12, 42, 22], [28, 10, 28, 18], [38, 146, 38, 163], [10, 163, 10, 146], [64, 66, 64, 66], [159,
    106, 159, 144], [138, 71, 138, 68], [103, 18, 103, 10], [128, 98, 128, 92], [163, 156, 163,
    157], [11, 22, 11, 12]]

private def lx4 : List ℕ := [0, 5, 7, 3, 9, 1, 6, 2, 10, 4, 8]

private theorem pl_x4 : pl (m11SdX ^ 4) = lx4 := by decide +kernel

private def W (i : ℕ) : List ℕ := m11bWords.getD i []
private def Lst (i : ℕ) : List ℕ := m11bLists.getD i []
private def par (i : ℕ) : ℕ := m11bPar.getD i 0
private def tab (i g : ℕ) : ℕ := (m11bTable.getD i []).getD g 0

private def inv165 (i : ℕ) : Perm (Fin 11) :=
  m11Eval (W i) * m11SdX ^ 4 * m11Eval (invWord (W i))

private theorem pl_inv165 (i : ℕ) :
    pl (inv165 i) = lcomp (lcomp (lprod (W i)) lx4) (lprod (invWord (W i))) := by
  simp only [inv165, pl_mul, pl_eval, pl_x4]

private theorem check_lists : ∀ i < 165,
    lcomp (lcomp (lprod (W i)) lx4) (lprod (invWord (W i))) = Lst i := by
  decide +kernel

private theorem check_closed : ∀ i < 165, ∀ g < 4,
    tab i g < 165 ∧ lcomp (lLetter g) (Lst i) = lcomp (Lst (tab i g)) (lLetter g) := by
  decide +kernel

private theorem check_parent : ∀ i < 165, 0 < i →
    par i < i ∧ lcomp (Lst (par i)) (Lst i) = lcomp (Lst i) (Lst (par i)) ∧
      Lst (par i) ≠ Lst i := by
  decide +kernel

end Data

section Abstract

private theorem pl_inv165_eq (i : ℕ) (hi : i < 165) : pl (inv165 i) = Lst i := by
  rw [pl_inv165]; exact check_lists i hi

private theorem inv165_zero : inv165 0 = m11SdX ^ 4 := by
  have h : W 0 = [] := rfl
  simp [inv165, h, invWord, m11Eval]

private theorem letter_conj (g : ℕ) (hg : g < 4) (i : ℕ) (hi : i < 165) :
    tab i g < 165 ∧ m11Letter g * inv165 i = inv165 (tab i g) * m11Letter g := by
  obtain ⟨h1, h2⟩ := check_closed i hi g hg
  refine ⟨h1, pl_injective ?_⟩
  rw [pl_mul, pl_mul, pl_letter, pl_inv165_eq i hi, pl_inv165_eq _ h1]
  exact h2

private theorem conj_mem_list {g : Perm (Fin 11)} (hg : g ∈ NativeSporadic.M11) :
    ∀ i < 165, (∃ j < 165, g * inv165 i * g⁻¹ = inv165 j) ∧
      (∃ j < 165, g⁻¹ * inv165 i * g = inv165 j) := by
  rw [m11_eq] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    intro i hi
    rcases hx with rfl | hx
    · obtain ⟨h0, e0⟩ := letter_conj 0 (by omega) i hi
      obtain ⟨h2, e2⟩ := letter_conj 2 (by omega) i hi
      refine ⟨⟨tab i 0, h0, ?_⟩, ⟨tab i 2, h2, ?_⟩⟩
      · exact mul_inv_eq_iff_eq_mul.mpr e0
      · have h : m11gA⁻¹ * inv165 i * (m11gA⁻¹)⁻¹ = inv165 (tab i 2) :=
          mul_inv_eq_iff_eq_mul.mpr e2
        rwa [inv_inv] at h
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      obtain ⟨h1, e1⟩ := letter_conj 1 (by omega) i hi
      obtain ⟨h3, e3⟩ := letter_conj 3 (by omega) i hi
      refine ⟨⟨tab i 1, h1, ?_⟩, ⟨tab i 3, h3, ?_⟩⟩
      · exact mul_inv_eq_iff_eq_mul.mpr e1
      · have h : m11gB⁻¹ * inv165 i * (m11gB⁻¹)⁻¹ = inv165 (tab i 3) :=
          mul_inv_eq_iff_eq_mul.mpr e3
        rwa [inv_inv] at h
  | one =>
    intro i hi
    exact ⟨⟨i, hi, by simp⟩, ⟨i, hi, by simp⟩⟩
  | mul x y _ _ ihx ihy =>
    intro i hi
    obtain ⟨⟨j, hj, ej⟩, ⟨j', hj', ej'⟩⟩ := ihy i hi
    obtain ⟨⟨k, hk, ek⟩, -⟩ := ihx j hj
    obtain ⟨-, ⟨k', hk', ek'⟩⟩ := ihx i hi
    obtain ⟨-, ⟨l, hl, el⟩⟩ := ihy k' hk'
    refine ⟨⟨k, hk, ?_⟩, ⟨l, hl, ?_⟩⟩
    · rw [← ek, ← ej]; group
    · rw [← el, ← ek']; group
  | inv x _ ihx =>
    intro i hi
    obtain ⟨h1, h2⟩ := ihx i hi
    exact ⟨by simpa using h2, by simpa using h1⟩

private theorem inv165_mem (i : ℕ) : inv165 i ∈ NativeSporadic.M11 :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ (m11Eval_mem _) (Subgroup.pow_mem _ m11SdX_mem 4))
    (m11Eval_mem _)

private def elt (i : ℕ) : ↥NativeSporadic.M11 := ⟨inv165 i, inv165_mem i⟩

private theorem elt_eq_conj (i : ℕ) :
    elt i = m11Conj (W i) * m11SdZ * (m11Conj (W i))⁻¹ := by
  apply Subtype.ext
  simp [elt, inv165, m11Conj, m11SdZ, m11Eval_invWord]

private theorem m11SdZ_orderOf : orderOf m11SdZ = 2 := by
  have h8 : m11SdX ^ 8 = 1 := m11SdX_pow_eight
  have h4 : m11SdX ^ 4 ≠ 1 := by decide +kernel
  refine orderOf_eq_prime ?_ ?_
  · apply Subtype.ext
    simpa [m11SdZ, ← pow_mul] using h8
  · intro h
    exact h4 (by simpa [m11SdZ] using congrArg Subtype.val h)

private theorem elt_orderOf (i : ℕ) : orderOf (elt i) = 2 := by
  rw [elt_eq_conj]
  have := orderOf_injective (MulAut.conj (m11Conj (W i))).toMonoidHom
    (MulAut.conj (m11Conj (W i))).injective m11SdZ
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  rw [this, m11SdZ_orderOf]

private theorem mem_list {u : ↥NativeSporadic.M11} (hu : orderOf u = 2) :
    ∃ i < 165, u = elt i := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_m11SdZ_of_orderOf_eq_two hu)
  have hu' : (u : Perm (Fin 11)) = (c : Perm (Fin 11)) * inv165 0 * (c : Perm (Fin 11))⁻¹ := by
    rw [← hc, inv165_zero]
    rfl
  obtain ⟨-, ⟨j, hj, ej⟩⟩ := conj_mem_list (g := (c : Perm (Fin 11))⁻¹) (Subgroup.inv_mem _ c.2)
    0 (by norm_num)
  refine ⟨j, hj, Subtype.ext ?_⟩
  rw [hu']
  rw [inv_inv] at ej
  exact ej

private theorem elt_adj (i : ℕ) (hi : i < 165) (h0 : 0 < i) : M11InvAdj (elt (par i)) (elt i) := by
  obtain ⟨hlt, hcomm, hne⟩ := check_parent i hi h0
  refine ⟨elt_orderOf _, elt_orderOf _, ?_, ?_⟩
  · intro h
    apply hne
    have h1 : inv165 (par i) = inv165 i := congrArg Subtype.val h
    rw [← pl_inv165_eq _ (by omega), ← pl_inv165_eq _ hi, h1]
  · apply Subtype.ext
    apply pl_injective
    change pl (inv165 (par i) * inv165 i) = pl (inv165 i * inv165 (par i))
    rw [pl_mul, pl_mul, pl_inv165_eq _ (by omega), pl_inv165_eq _ hi]
    exact hcomm

private theorem rtg_elt : ∀ j, j < 165 → Relation.ReflTransGen M11InvAdj (elt 0) (elt j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · exact Relation.ReflTransGen.refl
    · obtain ⟨hlt, -⟩ := check_parent j hj hpos
      exact (ih (par j) hlt (by omega)).tail (elt_adj j hj hpos)

private theorem adj_symm {a b : ↥NativeSporadic.M11} (h : M11InvAdj a b) : M11InvAdj b a :=
  ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.symm⟩

private theorem rtg_symm {a b : ↥NativeSporadic.M11} (h : Relation.ReflTransGen M11InvAdj a b) :
    Relation.ReflTransGen M11InvAdj b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (adj_symm hbc) ih

theorem m11_comm_connected {u v : ↥NativeSporadic.M11} (hu : orderOf u = 2)
    (hv : orderOf v = 2) : Relation.ReflTransGen M11InvAdj u v := by
  obtain ⟨i, hi, rfl⟩ := mem_list hu
  obtain ⟨j, hj, rfl⟩ := mem_list hv
  exact (rtg_symm (rtg_elt i hi)).trans (rtg_elt j hj)

end Abstract

end CFSG.ClassicalInvolution.Q3.Q3W
