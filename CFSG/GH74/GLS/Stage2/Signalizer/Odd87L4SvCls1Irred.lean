module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvCls1Frame

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification.CatFactsL4U4 CFSG.ComponentClassification.CatFactsL4U4.TBlocks
  CFSG.ComponentClassification.CatFactsL4U4.HBlocks CFSG.ComponentClassification.CatFactsL4U4.InvClassL
open scoped MatrixGroups commutatorElement

section Irred

variable {F : Type} [Field F]

theorem iota1_uuSL_mulVec (t : F) (w : Fin 4 → F) :
    ((iota1 (uuSL t) : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) *ᵥ w =
      ![w 0 + t * w 1, w 1, w 2, w 3] := by
  funext i
  fin_cases i <;> simp [coe_iota1, bd, coe_uuSL, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem iota1_llSL_mulVec (t : F) (w : Fin 4 → F) :
    ((iota1 (llSL t) : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) *ᵥ w =
      ![w 0, t * w 0 + w 1, w 2, w 3] := by
  funext i
  fin_cases i <;> simp [coe_iota1, bd, coe_llSL, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem swapM_mulVec (w : Fin 4 → F) : (swapM : Matrix (Fin 4) (Fin 4) F) *ᵥ w =
    ![w 2, w 3, w 0, w 1] := by
  funext i
  fin_cases i <;> simp [swapM, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem l4_cls1_irred_std (W : Submodule F (Fin 4 → F))
    (hW : ∀ A : SL(4, F), proj 4 F A ∈ fixSub (conjAut 4 F (B0 F)) →
      ∀ w ∈ W, (A : Matrix (Fin 4) (Fin 4) F) *ᵥ w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  have hU : ∀ t : F, ∀ w ∈ W, (t * w 1) • (Pi.single 0 1 : Fin 4 → F) ∈ W := by
    intro t w hw
    have h := W.sub_mem (hW (iota1 (uuSL t)) (proj_iota1_mem _) w hw) hw
    rw [iota1_uuSL_mulVec] at h
    convert h using 1
    funext i
    fin_cases i <;> simp
  have hL : ∀ t : F, ∀ w ∈ W, (t * w 0) • (Pi.single 1 1 : Fin 4 → F) ∈ W := by
    intro t w hw
    have h := W.sub_mem (hW (iota1 (llSL t)) (proj_iota1_mem _) w hw) hw
    rw [iota1_llSL_mulVec] at h
    convert h using 1
    funext i
    fin_cases i <;> simp
  have hS : ∀ w ∈ W, ![w 2, w 3, w 0, w 1] ∈ W := fun w hw => by
    rw [← swapM_mulVec]
    exact hW swapSL proj_swapSL_mem w hw
  have hfirst : ∀ w ∈ W, (w 0 ≠ 0 ∨ w 1 ≠ 0) →
      (Pi.single 0 1 : Fin 4 → F) ∈ W ∧ (Pi.single 1 1 : Fin 4 → F) ∈ W := by
    intro w hw h
    rcases h with h0 | h1
    · have he1 : (Pi.single 1 1 : Fin 4 → F) ∈ W := by
        have := W.smul_mem (w 0)⁻¹ (hL 1 w hw)
        rwa [smul_smul, one_mul, inv_mul_cancel₀ h0, one_smul] at this
      have he0 : (Pi.single 0 1 : Fin 4 → F) ∈ W := by
        have := hU 1 _ he1
        simpa using this
      exact ⟨he0, he1⟩
    · have he0 : (Pi.single 0 1 : Fin 4 → F) ∈ W := by
        have := W.smul_mem (w 1)⁻¹ (hU 1 w hw)
        rwa [smul_smul, one_mul, inv_mul_cancel₀ h1, one_smul] at this
      have he1 : (Pi.single 1 1 : Fin 4 → F) ∈ W := by
        have := hL 1 _ he0
        simpa using this
      exact ⟨he0, he1⟩
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hw, hw0⟩ : ∃ w ∈ W, w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hbot (eq_bot_iff.mpr fun w hw => by simpa using hcon w hw)
  have hfirst' : (Pi.single 0 1 : Fin 4 → F) ∈ W ∧ (Pi.single 1 1 : Fin 4 → F) ∈ W := by
    by_cases hc : w 0 ≠ 0 ∨ w 1 ≠ 0
    · exact hfirst w hw hc
    · push Not at hc
      have hc2 : w 2 ≠ 0 ∨ w 3 ≠ 0 := by
        by_contra hcon
        push Not at hcon
        apply hw0
        funext i
        fin_cases i <;> simp [hc.1, hc.2, hcon.1, hcon.2]
      exact hfirst _ (hS w hw) (by simpa using hc2)
  obtain ⟨he0, he1⟩ := hfirst'
  have he2 : (Pi.single 2 1 : Fin 4 → F) ∈ W := by
    have := hS _ he0
    convert this using 1
    funext i
    fin_cases i <;> simp
  have he3 : (Pi.single 3 1 : Fin 4 → F) ∈ W := by
    have := hS _ he1
    convert this using 1
    funext i
    fin_cases i <;> simp
  rw [eq_top_iff]
  intro v _
  have hv : v = v 0 • (Pi.single 0 1 : Fin 4 → F) + v 1 • (Pi.single 1 1 : Fin 4 → F) +
      v 2 • (Pi.single 2 1 : Fin 4 → F) + v 3 • (Pi.single 3 1 : Fin 4 → F) := by
    funext i
    fin_cases i <;> simp
  rw [hv]
  exact W.add_mem (W.add_mem (W.add_mem (W.smul_mem _ he0) (W.smul_mem _ he1)) (W.smul_mem _ he2))
    (W.smul_mem _ he3)

end Irred

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
