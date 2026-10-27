module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InvClassLb
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification.CatFactsL4U4 CFSG.ComponentClassification.CatFactsL4U4.TBlocks
  CFSG.ComponentClassification.CatFactsL4U4.HBlocks CFSG.ComponentClassification.CatFactsL4U4.InvClassL
open scoped MatrixGroups commutatorElement

section Frame

variable {F : Type} [Field F]

theorem X1_one_mul_self : (X1 (1 : F)) * X1 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [X1, Matrix.mul_apply, Fin.sum_univ_four]

@[expose] def B0 (F : Type) [Field F] : GL (Fin 4) F := ⟨X1 1, X1 1, X1_one_mul_self, X1_one_mul_self⟩

theorem coe_B0 : ((B0 F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = X1 1 := rfl

theorem coe_B0_inv : (((B0 F)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = X1 1 := rfl

theorem exists_frame_cls1 (h2 : (2 : F) ≠ 0) {B : GL (Fin 4) F} (hB : B * B = 1)
    (hr : Module.finrank F (LinearMap.ker (toLin' B.val - 1)) = 2) :
    ∃ P : GL (Fin 4) F, B = P * B0 F * P⁻¹ := by
  have hK : ringChar F ≠ 2 := fun h => h2 (by
    have := ringChar.spec F
    rw [h] at this
    exact_mod_cast (this 2).mpr (dvd_refl 2))
  have hXX : (B : Matrix (Fin 4) (Fin 4) F) * B = 1 := by
    rw [← Units.val_mul, hB, Units.val_one]
  have hc := isCompl_eigenspaces hK hXX
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  rw [Module.finrank_fin_fun, hr] at hsum
  have hr' : Module.finrank F (LinearMap.ker (toLin' B.val + 1)) = 2 := by omega
  have hTp : ∀ v ∈ LinearMap.ker (toLin' B.val - 1), toLin' B.val v = (1 : F) • v := fun v hv => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
    rw [one_smul, hv]
  have hTm : ∀ v ∈ LinearMap.ker (toLin' B.val + 1), toLin' B.val v = (-1 : F) • v := fun v hv => by
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply,
      add_eq_zero_iff_eq_neg] at hv
    rw [neg_one_smul, hv]
  have hdetT := det_eq_of_isCompl_smul hc hTp hTm
  rw [LinearMap.det_toLin', hr, hr'] at hdetT
  have hdet : (B : Matrix (Fin 4) (Fin 4) F).det = 1 := by
    rw [hdetT]
    norm_num
  have h1 : (B : Matrix (Fin 4) (Fin 4) F) ≠ 1 := by
    intro h
    have : LinearMap.ker (toLin' B.val - 1) = ⊤ := by
      rw [eq_top_iff]
      intro v _
      rw [LinearMap.mem_ker, h]
      simp
    rw [this, finrank_top, Module.finrank_fin_fun] at hr
    omega
  have hm1 : (B : Matrix (Fin 4) (Fin 4) F) ≠ -1 := by
    intro h
    have : LinearMap.ker (toLin' B.val - 1) = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [LinearMap.mem_ker, h] at hv
      rw [Submodule.mem_bot]
      funext i
      have := congrFun hv i
      simp at this
      have h4 : (2 : F) * v i = 0 := by linear_combination -this
      exact (mul_eq_zero.mp h4).resolve_left h2
    rw [this, finrank_bot] at hr
    omega
  obtain ⟨P, hP⟩ := exists_frame_t2_L4 h2 hXX hdet h1 hm1
  refine ⟨P, ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_B0]
  exact hP

theorem proj_mem_fixSub_of_comm {g : SL(4, F)}
    (h : (g : Matrix (Fin 4) (Fin 4) F) * X1 1 = X1 1 * (g : Matrix (Fin 4) (Fin 4) F)) :
    proj 4 F g ∈ fixSub (conjAut 4 F (B0 F)) := by
  rw [mem_fixSub, conjAut_proj]
  congr 1
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have h1 := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M i j)
    (show (X1 (1 : F)) * (g : Matrix (Fin 4) (Fin 4) F) * X1 1 = (g : Matrix (Fin 4) (Fin 4) F) by
      rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, X1_one_mul_self, Matrix.one_mul])
  rw [coe_slConjugation, coe_B0, coe_B0_inv]
  exact h1

theorem proj_mem_fixSub_of_anticomm {g : SL(4, F)}
    (h : (g : Matrix (Fin 4) (Fin 4) F) * X1 1 = -(X1 1 * (g : Matrix (Fin 4) (Fin 4) F))) :
    proj 4 F g ∈ fixSub (conjAut 4 F (B0 F)) := by
  rw [mem_fixSub, conjAut_proj]
  have hsl : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F (B0 F) g =
      g * negOne4 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have h1 := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M i j)
      (show (X1 (1 : F)) * (g : Matrix (Fin 4) (Fin 4) F) * X1 1 = -(g : Matrix (Fin 4) (Fin 4) F) by
        rw [Matrix.mul_assoc, h, Matrix.mul_neg, ← Matrix.mul_assoc, X1_one_mul_self,
          Matrix.one_mul])
    rw [coe_slConjugation, coe_B0, coe_B0_inv, Matrix.SpecialLinearGroup.coe_mul]
    have hn : ((negOne4 : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = -1 := rfl
    rw [hn, Matrix.mul_neg, Matrix.mul_one]
    exact h1
  rw [hsl, map_mul, proj_negOne4, mul_one]

@[expose] def iota1 : SL(2, F) →* SL(4, F) := (bdSL (F := F)).comp (MonoidHom.inl _ _)

theorem coe_iota1 (g : SL(2, F)) :
    ((iota1 g : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = bd (g : Matrix (Fin 2) (Fin 2) F) 1 := rfl

theorem proj_iota1_mem (g : SL(2, F)) : proj 4 F (iota1 g) ∈ fixSub (conjAut 4 F (B0 F)) :=
  proj_mem_fixSub_of_comm (bdSL_comm (g, 1))

@[expose] def iota2 : SL(2, F) →* SL(4, F) := (bdSL (F := F)).comp (MonoidHom.inr _ _)

@[expose] def uuSL (c : F) : SL(2, F) := ⟨uu c, det_uu c⟩

@[expose] def llSL (c : F) : SL(2, F) := ⟨ll c, det_ll c⟩

theorem coe_uuSL (c : F) : ((uuSL c : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, c; 0, 1] := rfl

theorem coe_llSL (c : F) : ((llSL c : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; c, 1] := rfl

@[expose] def swapM : Matrix (Fin 4) (Fin 4) F :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

theorem det_swapM : (swapM : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  rw [swapM, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]

@[expose] def swapSL : SL(4, F) := ⟨swapM, det_swapM⟩

theorem coe_swapSL : ((swapSL : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = swapM := rfl

theorem proj_swapSL_mem : proj 4 F (swapSL : SL(4, F)) ∈ fixSub (conjAut 4 F (B0 F)) := by
  refine proj_mem_fixSub_of_anticomm ?_
  rw [coe_swapSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapM, X1, Matrix.mul_apply, Fin.sum_univ_four]

end Frame

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
