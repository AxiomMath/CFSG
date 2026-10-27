module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Shape
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeMain

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Subgroup CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem l1_plus (hset : StandardSetting G L) (hZ : center L = ⊥)
    (h : CFSG.Blueprint.LieModel (L ⧸ center L) .POmegaPlus 4 2 1) :
    InvolutionsInOddPart L ∧ ∃ t ∈ centralizer (L : Set G), orderOf t = 2 ∧ t ∉ L ∧
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t ∧
      L ≤ centralizer ({t} : Set G) ∧ centralizer ({t} : Set G) ≤ normalizer (L : Set G) ∧
      (ShapeA t L ∨ ∃ h ∈ centralizer ({t} : Set G), ∀ m ∈ L, ∃ x ∈ L,
        h * x * h⁻¹ ≠ m * x * m⁻¹) :=
  ⟨involutionsInOddPart_of_center_eq_bot hZ h,
    l1 hset hZ (hypothesisOne_of_lieModel h) (foursGroupCondition_of_center_eq_bot hZ h)⟩

theorem l1_minus (hset : StandardSetting G L)
    (hZ : center L = ⊥) (h : CFSG.Blueprint.LieModel L .POmegaMinus 4 2 1) :
    InvolutionsInOddPart L ∧ ∃ t ∈ centralizer (L : Set G), orderOf t = 2 ∧ t ∉ L ∧
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t ∧
      L ≤ centralizer ({t} : Set G) ∧ centralizer ({t} : Set G) ≤ normalizer (L : Set G) ∧
      (ShapeA t L ∨ ∃ h ∈ centralizer ({t} : Set G), ∀ m ∈ L, ∃ x ∈ L,
        h * x * h⁻¹ ≠ m * x * m⁻¹) :=
  ⟨OmegaEightMinus.involutionsInOddPart_of_lieModel_minus h,
    l1 hset hZ (OmegaEightMinus.hypothesisOne_quotientCenter_of_lieModel_minus h)
      (OmegaEightMinus.foursGroupCondition_of_lieModel_minus h)⟩

end CFSG.EvenSmallLie.OmegaEight.Stage1
