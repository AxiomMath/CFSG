module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG

theorem sign_eq_signAux {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    σ.sign = σ.signAux := by
  refine σ.swap_induction_on (by simp) fun π i j hne h_eq => ?_
  rw [Equiv.Perm.signAux_mul, Equiv.Perm.sign_mul, h_eq, Equiv.Perm.sign_swap hne,
    Equiv.Perm.signAux_swap hne]

@[expose] def isEvenPerm5 (x : Equiv.Perm (Fin 5)) : Bool := x.signAux == 1

theorem mem_alternatingGroup_five_iff (x : Equiv.Perm (Fin 5)) :
    x ∈ alternatingGroup (Fin 5) ↔ isEvenPerm5 x = true := by
  rw [Equiv.Perm.mem_alternatingGroup, sign_eq_signAux, isEvenPerm5, beq_iff_eq]

theorem isEvenPerm5_cube_eq_one_of_beq_false (g : Equiv.Perm (Fin 5))
    (hg : isEvenPerm5 g = true) (a b : Fin 5) (hab : (a == b) = false)
    (ha : g a = a) (hb : g b = b) : g ^ 3 = 1 := by
  revert g a b
  decide +kernel

theorem alternatingGroup_cube_eq_one_of_fixes_two (g : Equiv.Perm (Fin 5))
    (hg : g ∈ alternatingGroup (Fin 5)) (a b : Fin 5) (hab : a ≠ b)
    (ha : g a = a) (hb : g b = b) : g ^ 3 = 1 := by
  exact isEvenPerm5_cube_eq_one_of_beq_false g
    ((mem_alternatingGroup_five_iff g).mp hg) a b (beq_false_of_ne hab) ha hb

theorem isEvenPerm5_eq_one_of_beq_false (g : Equiv.Perm (Fin 5))
    (hg : isEvenPerm5 g = true) (a b c : Fin 5)
    (hab : (a == b) = false) (hac : (a == c) = false) (hbc : (b == c) = false)
    (ha : g a = a) (hb : g b = b) (hc : g c = c) : g = 1 := by
  revert g a b c
  decide +kernel

theorem alternatingGroup_eq_one_of_fixes_three (g : Equiv.Perm (Fin 5))
    (hg : g ∈ alternatingGroup (Fin 5)) (a b c : Fin 5)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : g a = a) (hb : g b = b) (hc : g c = c) : g = 1 := by
  exact isEvenPerm5_eq_one_of_beq_false g
    ((mem_alternatingGroup_five_iff g).mp hg) a b c (beq_false_of_ne hab)
    (beq_false_of_ne hac) (beq_false_of_ne hbc) ha hb hc

end CFSG

end
