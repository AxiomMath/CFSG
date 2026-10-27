module

public import CFSG.GH74.GLS.Stage1.Thm6.M12Facts.Extra

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.M12Facts

open Subgroup CFSG.GH74.GLS.Stage1.Thm6.Sec13

@[expose] def xNF : NF := (0, 0, 0, 1)
@[expose] def yNF : NF := (0, 0, 1, 0)
@[expose] def xyNF : NF := (0, 0, 1, 1)

@[expose] def pInvY (p : NF) : Prop := nfMul p p = (0, 0, 0, 0) ∧ p.2.2.1 = 1 ∧ p.2.2.2 = 0

@[expose] def pInvXY (p : NF) : Prop := nfMul p p = (0, 0, 0, 0) ∧ p.2.2.1 = 1 ∧ p.2.2.2 = 1

instance : DecidablePred pInvY := fun p => by unfold pInvY; infer_instance
instance : DecidablePred pInvXY := fun p => by unfold pInvXY; infer_instance

theorem inv_class_y : ∀ p : NF, pInvY p → ∃ q : NF, pH0 q ∧ nfMul (nfMul q yNF) (nfInv q) = p := by
  decide +kernel

theorem inv_class_xy : ∀ p : NF, pInvXY p →
    ∃ q : NF, pH0 q ∧ nfMul (nfMul q xyNF) (nfInv q) = p := by decide +kernel

theorem pH0_of_sq_ne : ∀ p : NF, pQ0 p → nfMul p p ≠ (0, 0, 0, 0) → pH0 p := by decide +kernel

theorem pU_sq : ∀ p : NF, pH0 p → pU (nfMul p p) := by decide +kernel

theorem pU_mem_list : ∀ p : NF, pU p →
    p ∈ ([(0, 0, 0, 0), zNF, (2, 0, 0, 0), (0, 2, 0, 0)] : List NF) := by decide +kernel

theorem pU_cases (p : NF) (hp : pU p) :
    p = (0, 0, 0, 0) ∨ p = zNF ∨ p = (2, 0, 0, 0) ∨ p = (0, 2, 0, 0) := by
  simpa using pU_mem_list p hp

theorem pU_sq_one : ∀ p : NF, pU p → nfMul p p = (0, 0, 0, 0) := by decide +kernel

theorem pR_of_pU : ∀ p : NF, pU p → pR p := by decide +kernel

theorem not_pQ1_x : ¬ pQ1 xNF := by decide +kernel
theorem cosets_Q0 : ∀ pu p : NF, ¬ pQ0 pu → pQ0 p ∨ pQ0 (nfMul (nfInv pu) p) := by decide +kernel
theorem cosets_Q1 : ∀ pu p : NF, ¬ pQ1 pu → pQ1 p ∨ pQ1 (nfMul (nfInv pu) p) := by decide +kernel

theorem cyc_Q0 : ∀ p : NF, ¬ pQ0 p → pQ0 (nfMul (nfInv yNF) p) := by decide +kernel
theorem cyc_Q1 : ∀ p : NF, ¬ pQ1 p → pQ1 (nfMul (nfInv yNF) p) := by decide +kernel

theorem pU_square : ∀ p : NF, pU p → ∃ q : NF, pH0 q ∧ nfMul q q = p := by decide +kernel

theorem U_swap_a : nfMul (nfMul yNF (2, 0, 0, 0)) (nfInv yNF) = (0, 2, 0, 0) := by decide +kernel

theorem U_swap_b : nfMul (nfMul yNF (0, 2, 0, 0)) (nfInv yNF) = (2, 0, 0, 0) := by decide +kernel

section
variable {G : Type*} [Group G] {S : Subgroup G} {a b y x : G} (h : M12Data S a b y x)
include h

theorem z_central {s : G} (hs : s ∈ S) : s * (a ^ 2 * b ^ 2) = (a ^ 2 * b ^ 2) * s := by
  obtain ⟨p, rfl⟩ := exists_nf h hs
  rw [zG_eq (y := y) (x := x), nu_mul h, nu_mul h, zNF_central p]

theorem z_sq : (a ^ 2 * b ^ 2) * (a ^ 2 * b ^ 2) = 1 := by
  rw [zG_eq (y := y) (x := x), nu_mul h, zNF_sq, nu_zero]

theorem z_ne_one : a ^ 2 * b ^ 2 ≠ 1 := by
  intro e
  rw [zG_eq (y := y) (x := x), ← nu_zero (a := a) (b := b) (y := y) (x := x)] at e
  exact absurd (nu_injective h e) (by decide)

theorem z_mem : a ^ 2 * b ^ 2 ∈ S := by
  rw [zG_eq (y := y) (x := x)]; exact nu_mem h _

end

end CFSG.GH74.GLS.Stage1.Thm6.M12Facts
