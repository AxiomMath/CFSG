module

public import CFSG.ClassicalInvolution.RouteD.Basic

public section

namespace CFSG.ClassicalInvolution.RouteD

open TauCeti

variable {n : ℕ}

theorem A_eq_neg_one_iff (i j : Fin n) :
    CartanMatrix.A n i j = -1 ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  unfold CartanMatrix.A
  simp only [Matrix.of_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : i.val ≠ j.val := fun e => h (Fin.ext e)
    simp only [h, ite_false]
    by_cases hc : i.val + 1 = j.val ∨ j.val + 1 = i.val <;> simp [hc]

theorem A_eq_zero_iff (i j : Fin n) :
    CartanMatrix.A n i j = 0 ↔ (i ≠ j ∧ ¬(i.val + 1 = j.val ∨ j.val + 1 = i.val)) := by
  unfold CartanMatrix.A
  simp only [Matrix.of_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : i.val ≠ j.val := fun e => h (Fin.ext e)
    simp only [h, ite_false]
    by_cases hc : i.val + 1 = j.val ∨ j.val + 1 = i.val <;> simp [hc, h]

theorem B_eq_neg_one_iff (i j : Fin n) :
    CartanMatrix.B n i j = -1 ↔ ((i.val + 1 = j.val ∧ j.val ≠ n - 1) ∨ j.val + 1 = i.val) := by
  unfold CartanMatrix.B
  simp only [Matrix.of_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : i.val ≠ j.val := fun e => h (Fin.ext e)
    simp only [h, ite_false]
    split_ifs <;> simp <;> omega

theorem B_eq_neg_two_iff (i j : Fin n) :
    CartanMatrix.B n i j = -2 ↔ (i.val + 1 = j.val ∧ j.val = n - 1) := by
  unfold CartanMatrix.B
  simp only [Matrix.of_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : i.val ≠ j.val := fun e => h (Fin.ext e)
    simp only [h, ite_false]
    split_ifs <;> simp <;> omega

theorem B_eq_zero_iff (i j : Fin n) :
    CartanMatrix.B n i j = 0 ↔ (i ≠ j ∧ ¬ i.val + 1 = j.val ∧ ¬ j.val + 1 = i.val) := by
  unfold CartanMatrix.B
  simp only [Matrix.of_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : i.val ≠ j.val := fun e => h (Fin.ext e)
    simp only [h, ite_false]
    split_ifs <;> simp [h] <;> omega

theorem C_eq_neg_one_iff (i j : Fin n) :
    CartanMatrix.C n i j = -1 ↔ (i.val + 1 = j.val ∨ (j.val + 1 = i.val ∧ i.val ≠ n - 1)) := by
  unfold CartanMatrix.C
  simp only [Matrix.of_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : i.val ≠ j.val := fun e => h (Fin.ext e)
    simp only [h, ite_false]
    split_ifs <;> simp <;> omega

theorem C_eq_neg_two_iff (i j : Fin n) :
    CartanMatrix.C n i j = -2 ↔ (j.val + 1 = i.val ∧ i.val = n - 1) := by
  unfold CartanMatrix.C
  simp only [Matrix.of_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : i.val ≠ j.val := fun e => h (Fin.ext e)
    simp only [h, ite_false]
    split_ifs <;> simp <;> omega

theorem C_eq_zero_iff (i j : Fin n) :
    CartanMatrix.C n i j = 0 ↔ (i ≠ j ∧ ¬ i.val + 1 = j.val ∧ ¬ j.val + 1 = i.val) := by
  unfold CartanMatrix.C
  simp only [Matrix.of_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : i.val ≠ j.val := fun e => h (Fin.ext e)
    simp only [h, ite_false]
    split_ifs <;> simp [h] <;> omega

@[expose] def DAdj (n : ℕ) (i j : Fin n) : Prop :=
  (i.val + 1 = j.val ∧ j.val + 2 < n) ∨ (j.val + 1 = i.val ∧ i.val + 2 < n) ∨
    (i.val + 3 = n ∧ (j.val + 2 = n ∨ j.val + 1 = n)) ∨
    (j.val + 3 = n ∧ (i.val + 2 = n ∨ i.val + 1 = n))

theorem D_eq_neg_one_iff (i j : Fin n) : CartanMatrix.D n i j = -1 ↔ DAdj n i j := by
  unfold CartanMatrix.D DAdj
  simp only [Matrix.of_apply]
  by_cases h : i = j
  · subst h; simp; omega
  · have h' : i.val ≠ j.val := fun e => h (Fin.ext e)
    simp only [h, ite_false]
    split_ifs <;> simp <;> omega

theorem D_eq_zero_iff (i j : Fin n) : CartanMatrix.D n i j = 0 ↔ (i ≠ j ∧ ¬ DAdj n i j) := by
  unfold CartanMatrix.D DAdj
  simp only [Matrix.of_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : i.val ≠ j.val := fun e => h (Fin.ext e)
    simp only [h, ite_false]
    split_ifs <;> simp [h] <;> omega

theorem DAdj_symm (i j : Fin n) : DAdj n i j ↔ DAdj n j i := by
  unfold DAdj; omega

end CFSG.ClassicalInvolution.RouteD
