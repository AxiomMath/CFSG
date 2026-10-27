module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage0Model
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1L1
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage0Split

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage0

open Subgroup CFSG.EvenSmallLie.OmegaEight.Stage1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_shape_plus (hset : StandardSetting G L)
    (hZ : center L = ⊥) (h : CFSG.Blueprint.LieModel (L ⧸ center L) .POmegaPlus 4 2 1) :
    InvolutionsInOddPart L ∧ ∃ t, StepK t L ∧
      (ShapeA t L ∨ (∃ r, ShapeB t L r) ∨ (∃ b, ShapeC t L b) ∨ (∃ b r, ShapeD t L b r) ∨
        (∃ c, ShapeC' t L c) ∨ ∃ c r, ShapeD' t L c r) := by
  obtain ⟨hodd, t, htC, ht, htL, hKer, hLt, hHN, -⟩ := l1_plus hset hZ h
  have hK : StepK t L := ⟨ht, htC, htL, hKer, hLt, hHN⟩
  refine ⟨hodd, t, hK, hK.exists_shape (involutionLifting_plus hZ h) ?_⟩
  rw [← card_outer_plus hZ h]
  exact hK.relIndex_dvd_card_outer

theorem exists_shape_minus (hset : StandardSetting G L)
    (hZ : center L = ⊥) (h : CFSG.Blueprint.LieModel L .POmegaMinus 4 2 1) :
    InvolutionsInOddPart L ∧ ∃ t, StepK t L ∧
      (ShapeA t L ∨ (∃ b, ShapeC t L b) ∨ ∃ c, ShapeC' t L c) := by
  obtain ⟨hodd, t, htC, ht, htL, hKer, hLt, hHN, -⟩ := l1_minus hset hZ h
  have hK : StepK t L := ⟨ht, htC, htL, hKer, hLt, hHN⟩
  refine ⟨hodd, t, hK, hK.exists_shape_of_dvd_two (involutionLifting_minus h) ?_⟩
  rw [← card_outer_minus h]
  exact hK.relIndex_dvd_card_outer

end CFSG.EvenSmallLie.OmegaEight.Stage0
