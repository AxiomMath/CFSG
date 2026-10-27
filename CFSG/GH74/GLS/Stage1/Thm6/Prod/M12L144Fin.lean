module

public import CFSG.GH74.GLS.Stage1.Thm6.M12Facts.Classes

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.M12Facts

open Subgroup CFSG.GH74.GLS.Stage1.Thm6.Sec13

@[expose] def pZc (p : NF) : Prop :=
  p.2.2.1 = 0 ∧ p.2.2.2 = 1 ∧ p.1.val % 2 = 1 ∧ p.2.1.val % 2 = 1

instance : DecidablePred pZc := fun p => by unfold pZc; infer_instance

@[expose] def pXcl (p : NF) : Prop :=
  ∃ q : NF, nfMul (nfMul q xNF) (nfInv q) = p ∨ nfMul (nfMul q yNF) (nfInv q) = p ∨
    nfMul (nfMul q xyNF) (nfInv q) = p

instance : DecidablePred pXcl := fun p => by unfold pXcl; infer_instance

@[expose] def pInvR (p : NF) : Prop :=
  pR p ∧ nfMul p p = (0, 0, 0, 0) ∧ p ≠ (0, 0, 0, 0) ∧ p ≠ zNF ∧ p ≠ (2, 0, 0, 0) ∧
    p ≠ (0, 2, 0, 0)

instance : DecidablePred pInvR := fun p => by unfold pInvR; infer_instance

theorem inv_R_split : ∀ p : NF, pInvR p → pXcl p ∨ pZc p := by decide +kernel

theorem zc_conj : ∀ p q : NF, pZc p → pZc q →
    ∃ r : NF, pH0 r ∧ nfMul (nfMul r p) (nfInv r) = q := by decide +kernel

theorem sq_ne_zero : ∀ i j : Fin 4, ¬ (i.val % 2 = 0 ∧ j.val % 2 = 0) →
    nfMul (i, j, 0, 0) (i, j, 0, 0) ≠ (0, 0, 0, 0) := by decide +kernel

theorem pU_sq_H0 : ∀ i j : Fin 4, pU (nfMul (i, j, 0, 0) (i, j, 0, 0)) := by decide +kernel

theorem sq_eq_zNF_odd : ∀ q : NF, pH0 q → nfMul q q = zNF →
    q.1.val % 2 = 1 ∧ q.2.1.val % 2 = 1 := by decide +kernel

theorem pZc_mul_x : ∀ q : NF, pH0 q → q.1.val % 2 = 1 → q.2.1.val % 2 = 1 →
    pZc (nfMul q xNF) := by decide +kernel

theorem mul_x_eq : ∀ i j : Fin 4, nfMul (i, j, 0, 0) xNF = (i, j, 0, 1) := by decide +kernel

theorem nfInv_a2 : nfInv (2, 0, 0, 0) = (2, 0, 0, 0) := by decide +kernel

theorem a2_mul_a2 : nfMul (2, 0, 0, 0) (0, 2, 0, 0) = zNF := by decide +kernel

theorem a2_mul_a2' : nfMul (2, 0, 0, 0) (2, 0, 0, 0) = (0, 0, 0, 0) := by decide +kernel

theorem a2_ne_one : ((2, 0, 0, 0) : NF) ≠ (0, 0, 0, 0) := by decide +kernel

theorem a2_ne_z : ((2, 0, 0, 0) : NF) ≠ zNF := by decide +kernel

theorem pU_a2 : pU ((2, 0, 0, 0) : NF) := by decide +kernel

theorem pH0_ij (i j : Fin 4) : pH0 ((i, j, 0, 0) : NF) := ⟨rfl, rfl⟩

end CFSG.GH74.GLS.Stage1.Thm6.M12Facts
