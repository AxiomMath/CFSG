module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvCls1Frame

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification.CatFactsL4U4 CFSG.ComponentClassification.CatFactsL4U4.TBlocks
  CFSG.ComponentClassification.CatFactsL4U4.HBlocks CFSG.ComponentClassification.CatFactsL4U4.InvClassL
open scoped MatrixGroups commutatorElement

section Cent

variable {F : Type} [Field F]

theorem comm_X1_of_comm_blocks {x : Matrix (Fin 4) (Fin 4) F}
    (hu : x * bd (uu (1 : F)) 1 = bd (uu 1) 1 * x) (hl : x * bd (ll (1 : F)) 1 = bd (ll 1) 1 * x) :
    x * X1 1 = X1 1 * x := by
  have e1 := congrFun (congrFun hu 2) 1
  have e2 := congrFun (congrFun hu 3) 1
  have e3 := congrFun (congrFun hu 0) 2
  have e4 := congrFun (congrFun hu 0) 3
  have f1 := congrFun (congrFun hl 2) 0
  have f2 := congrFun (congrFun hl 3) 0
  have f3 := congrFun (congrFun hl 1) 2
  have f4 := congrFun (congrFun hl 1) 3
  simp [bd, uu, ll, Matrix.mul_apply, Fin.sum_univ_four] at e1 e2 e3 e4 f1 f2 f3 f4
  ext i j
  fin_cases i <;> fin_cases j <;> simp [X1, Matrix.mul_apply, Fin.sum_univ_four, e1, e2, e3, e4, f1, f2, f3, f4]

theorem l4_cls1_cent_std (x : SL(4, F))
    (h : ∀ ι : SL(2, F) →* SL(4, F), (∀ g, proj 4 F (ι g) ∈ fixSub (conjAut 4 F (B0 F))) →
      ∀ g, x * ι g = ι g * x) :
    conjAut 4 F (B0 F) (proj 4 F x) = proj 4 F x := by
  have hu := congrArg Subtype.val (h iota1 proj_iota1_mem (uuSL 1))
  have hl := congrArg Subtype.val (h iota1 proj_iota1_mem (llSL 1))
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_iota1] at hu hl
  have hcomm := comm_X1_of_comm_blocks (x := (x : Matrix (Fin 4) (Fin 4) F)) hu hl
  exact mem_fixSub.mp (proj_mem_fixSub_of_comm hcomm)

@[expose] def dAlt (F : Type) [Field F] : SL(4, F) :=
  ⟨diagonal ![-1, 1, -1, 1], by simp [Matrix.det_diagonal, Fin.prod_univ_four]⟩

theorem coe_dAlt : ((dAlt F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = diagonal ![-1, 1, -1, 1] := rfl

theorem proj_dAlt_mem : proj 4 F (dAlt F) ∈ fixSub (conjAut 4 F (B0 F)) := by
  refine proj_mem_fixSub_of_comm ?_
  rw [coe_dAlt]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [X1, Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem comm_dAlt_uu (h3 : (3 : F) = 0) : ⁅dAlt F, iota1 (uuSL (1 : F))⁆ = iota1 (uuSL 1) := by
  have h : dAlt F * iota1 (uuSL (1 : F)) = iota1 (uuSL 1) * iota1 (uuSL 1) * dAlt F := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, coe_dAlt, coe_iota1]
    fin_cases i <;> fin_cases j <;>
      simp [bd, coe_uuSL, Matrix.mul_apply, Matrix.diagonal_apply]
    linear_combination (-1 : F) * h3
  calc ⁅dAlt F, iota1 (uuSL (1 : F))⁆ = dAlt F * iota1 (uuSL 1) * (dAlt F)⁻¹ * (iota1 (uuSL 1))⁻¹ := by
        rw [commutatorElement_def]
    _ = iota1 (uuSL 1) * iota1 (uuSL 1) * dAlt F * (dAlt F)⁻¹ * (iota1 (uuSL 1))⁻¹ := by rw [h]
    _ = iota1 (uuSL 1) := by group

theorem comm_dAlt_ll (h3 : (3 : F) = 0) : ⁅dAlt F, iota1 (llSL (1 : F))⁆ = iota1 (llSL 1) := by
  have h : dAlt F * iota1 (llSL (1 : F)) = iota1 (llSL 1) * iota1 (llSL 1) * dAlt F := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, coe_dAlt, coe_iota1]
    fin_cases i <;> fin_cases j <;>
      simp [bd, coe_llSL, Matrix.mul_apply, Matrix.diagonal_apply]
    linear_combination h3
  calc ⁅dAlt F, iota1 (llSL (1 : F))⁆ = dAlt F * iota1 (llSL 1) * (dAlt F)⁻¹ * (iota1 (llSL 1))⁻¹ := by
        rw [commutatorElement_def]
    _ = iota1 (llSL 1) * iota1 (llSL 1) * dAlt F * (dAlt F)⁻¹ * (iota1 (llSL 1))⁻¹ := by rw [h]
    _ = iota1 (llSL 1) := by group

theorem l4_cls1_cent3_std [Finite F] (hF : Nat.card F = 3) (x : SL(4, F))
    (h : ∀ a b : SL(4, F), proj 4 F a ∈ fixSub (conjAut 4 F (B0 F)) →
      proj 4 F b ∈ fixSub (conjAut 4 F (B0 F)) → x * ⁅a, b⁆ = ⁅a, b⁆ * x) :
    conjAut 4 F (B0 F) (proj 4 F x) = proj 4 F x := by
  have h3 : (3 : F) = 0 := by
    have := Fintype.ofFinite F
    have h0 := FiniteField.cast_card_eq_zero F
    rw [← Nat.card_eq_fintype_card, hF] at h0
    exact_mod_cast h0
  have hu := congrArg Subtype.val
    (h (dAlt F) (iota1 (uuSL 1)) proj_dAlt_mem (proj_iota1_mem _))
  have hl := congrArg Subtype.val
    (h (dAlt F) (iota1 (llSL 1)) proj_dAlt_mem (proj_iota1_mem _))
  rw [comm_dAlt_uu h3] at hu
  rw [comm_dAlt_ll h3] at hl
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_iota1] at hu hl
  have hcomm := comm_X1_of_comm_blocks (x := (x : Matrix (Fin 4) (Fin 4) F)) hu hl
  exact mem_fixSub.mp (proj_mem_fixSub_of_comm hcomm)

end Cent

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
