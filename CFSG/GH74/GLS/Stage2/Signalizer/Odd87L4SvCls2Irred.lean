module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvCls2Frame
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvConj

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatFactsL4U4.InvClassL
open scoped MatrixGroups commutatorElement

section Irred

variable {F : Type} [Field F]

theorem irr_step_up {c : F} (hc : ¬ IsSquare c) (W : Submodule F (Fin 4 → F))
    (hU : ∀ a b : F, ∀ w ∈ W, uMat c a b *ᵥ w ∈ W) {w : Fin 4 → F} (hw : w ∈ W)
    (hne : w 2 ≠ 0 ∨ w 3 ≠ 0) :
    (Pi.single 0 1 : Fin 4 → F) ∈ W ∧ (Pi.single 1 1 : Fin 4 → F) ∈ W := by
  have hD : w 2 ^ 2 - w 3 ^ 2 * c ≠ 0 := sq_sub_mul_ne_zero hc hne
  have t1 : uMat c 1 0 *ᵥ w - w ∈ W := W.sub_mem (hU 1 0 w hw) hw
  have t2 : uMat c 0 1 *ᵥ w - w ∈ W := W.sub_mem (hU 0 1 w hw) hw
  constructor
  · have : (Pi.single 0 1 : Fin 4 → F) =
        (w 2 ^ 2 - w 3 ^ 2 * c)⁻¹ • (w 2 • (uMat c 1 0 *ᵥ w - w) - w 3 • (uMat c 0 1 *ᵥ w - w)) := by
      ext i
      fin_cases i <;>
        simp [uMat_mulVec_zero, uMat_mulVec_one, uMat_mulVec_two, uMat_mulVec_three] <;>
        first | (field_simp; done) | (right; ring)
    rw [this]
    exact W.smul_mem _ (W.sub_mem (W.smul_mem _ t1) (W.smul_mem _ t2))
  · have : (Pi.single 1 1 : Fin 4 → F) =
        (w 2 ^ 2 - w 3 ^ 2 * c)⁻¹ •
          (-(c * w 3) • (uMat c 1 0 *ᵥ w - w) + w 2 • (uMat c 0 1 *ᵥ w - w)) := by
      ext i
      fin_cases i <;>
        simp [uMat_mulVec_zero, uMat_mulVec_one, uMat_mulVec_two, uMat_mulVec_three] <;>
        first | (field_simp; done) | (right; ring) | (field_simp; ring)
    rw [this]
    exact W.smul_mem _ (W.add_mem (W.smul_mem _ t1) (W.smul_mem _ t2))

theorem irr_step_low {c : F} (hc : ¬ IsSquare c) (W : Submodule F (Fin 4 → F))
    (hL : ∀ a b : F, ∀ w ∈ W, lMat c a b *ᵥ w ∈ W) {w : Fin 4 → F} (hw : w ∈ W)
    (hne : w 0 ≠ 0 ∨ w 1 ≠ 0) :
    (Pi.single 2 1 : Fin 4 → F) ∈ W ∧ (Pi.single 3 1 : Fin 4 → F) ∈ W := by
  have hD : w 0 ^ 2 - w 1 ^ 2 * c ≠ 0 := sq_sub_mul_ne_zero hc hne
  have t1 : lMat c 1 0 *ᵥ w - w ∈ W := W.sub_mem (hL 1 0 w hw) hw
  have t2 : lMat c 0 1 *ᵥ w - w ∈ W := W.sub_mem (hL 0 1 w hw) hw
  constructor
  · have : (Pi.single 2 1 : Fin 4 → F) =
        (w 0 ^ 2 - w 1 ^ 2 * c)⁻¹ • (w 0 • (lMat c 1 0 *ᵥ w - w) - w 1 • (lMat c 0 1 *ᵥ w - w)) := by
      ext i
      fin_cases i <;>
        simp [lMat_mulVec_zero, lMat_mulVec_one, lMat_mulVec_two, lMat_mulVec_three] <;>
        first | (field_simp; done) | (right; ring)
    rw [this]
    exact W.smul_mem _ (W.sub_mem (W.smul_mem _ t1) (W.smul_mem _ t2))
  · have : (Pi.single 3 1 : Fin 4 → F) =
        (w 0 ^ 2 - w 1 ^ 2 * c)⁻¹ •
          (-(c * w 1) • (lMat c 1 0 *ᵥ w - w) + w 0 • (lMat c 0 1 *ᵥ w - w)) := by
      ext i
      fin_cases i <;>
        simp [lMat_mulVec_zero, lMat_mulVec_one, lMat_mulVec_two, lMat_mulVec_three] <;>
        first | (field_simp; done) | (right; ring) | (field_simp; ring)
    rw [this]
    exact W.smul_mem _ (W.add_mem (W.smul_mem _ t1) (W.smul_mem _ t2))

theorem cls2_irred_frame (c : Fˣ) (hc : ¬ IsSquare (c : F)) (W : Submodule F (Fin 4 → F))
    (hW : ∀ A' : SL(4, F), proj 4 F A' ∈ fixSub (conjAut 4 F (stdGL c)) →
      ∀ w ∈ W, (A' : Matrix (Fin 4) (Fin 4) F) *ᵥ w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  refine Or.inr ?_
  have hU : ∀ a b : F, ∀ w ∈ W, uMat (c : F) a b *ᵥ w ∈ W := fun a b w hw =>
    hW (uSL (c : F) a b) (proj_mem_fixSub_of_mem_commSub c (uSL_mem_commSub _ a b)) w hw
  have hL : ∀ a b : F, ∀ w ∈ W, lMat (c : F) a b *ᵥ w ∈ W := fun a b w hw =>
    hW (lSL (c : F) a b) (proj_mem_fixSub_of_mem_commSub c (lSL_mem_commSub _ a b)) w hw
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hbasis : (Pi.single 0 1 : Fin 4 → F) ∈ W ∧ (Pi.single 1 1 : Fin 4 → F) ∈ W ∧
      (Pi.single 2 1 : Fin 4 → F) ∈ W ∧ (Pi.single 3 1 : Fin 4 → F) ∈ W := by
    by_cases h23 : w 2 ≠ 0 ∨ w 3 ≠ 0
    · obtain ⟨e0, e1⟩ := irr_step_up hc W hU hwW h23
      obtain ⟨e2, e3⟩ := irr_step_low hc W hL e0 (Or.inl (by simp))
      exact ⟨e0, e1, e2, e3⟩
    · push Not at h23
      have h01 : w 0 ≠ 0 ∨ w 1 ≠ 0 := by
        by_contra h
        push Not at h
        apply hw0
        ext i
        fin_cases i <;> simp [h.1, h.2, h23.1, h23.2]
      obtain ⟨e2, e3⟩ := irr_step_low hc W hL hwW h01
      obtain ⟨e0, e1⟩ := irr_step_up hc W hU e2 (Or.inl (by simp))
      exact ⟨e0, e1, e2, e3⟩
  rw [eq_top_iff, ← (Pi.basisFun F (Fin 4)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · simpa using hbasis.1
  · simpa using hbasis.2.1
  · simpa using hbasis.2.2.1
  · simpa using hbasis.2.2.2

theorem l4_cls2_irred (_hodd : Odd (Nat.card F)) {α : MulAut (projectiveSL 4 F)} {A : GL (Fin 4) F}
    {c : Fˣ} (hA : A * A = GeneralLinearGroup.scalar (Fin 4) c) (hc : ¬ IsSquare (c : F))
    (hα : α = conjAut 4 F A) (W : Submodule F (Fin 4 → F))
    (hW : ∀ A' : SL(4, F), proj 4 F A' ∈ fixSub α → ∀ w ∈ W,
      (A' : Matrix (Fin 4) (Fin 4) F) *ᵥ w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  obtain ⟨P, hP⟩ := exists_normal_form hA hc
  subst hα
  exact irred_transport P hP (fun W₀ hW₀ => cls2_irred_frame c hc W₀ hW₀) W hW

end Irred

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
