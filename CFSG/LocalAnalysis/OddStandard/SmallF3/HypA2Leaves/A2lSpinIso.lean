module

public import CFSG.ClassicalInvolution.WeakCT.TwistedSpinMap
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.WeakCT

section Coe

variable {K V₁ V₂ : Type*} [Field K] [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂]
  [Module K V₂] {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}

theorem a2l_coe_spinGroupMap_eq_neg_one (f : Q₁ →qᵢ Q₂) {x : spinGroup Q₁}
    (hx : (x : CliffordAlgebra Q₁) = -1) :
    ((f.spinGroupMap x : spinGroup Q₂) : CliffordAlgebra Q₂) = -1 := by
  rw [QuadraticMap.Isometry.coe_spinGroupMap_apply, hx, map_neg, map_one]

end Coe

section Irreducible

theorem a2l_irr_zero_one {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 3)
    (h2 : (2 : F) ≠ 0) : ∀ s : F, s ^ 2 + (0 : F) * s + 1 ≠ 0 := by
  intro s hs
  have h3 : s ^ 3 = s := by
    have := FiniteField.pow_card s
    rwa [hF] at this
  have hsq : s ^ 2 = -1 := by linear_combination hs
  have h4 : (2 : F) * s = 0 := by
    have : s ^ 3 = s * s ^ 2 := by ring
    rw [this, hsq] at h3
    linear_combination -h3
  have hs0 : s = 0 := (mul_eq_zero.1 h4).resolve_left h2
  rw [hs0] at hs
  simp at hs

end Irreducible

section MinusToOdd

variable (F : Type) [Field F]

@[expose] def a2lOddIdx : Fin 3 ⊕ Fin 3 ⊕ Unit → Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2
  | .inl i => ![Sum.inl (0 : Fin 2), Sum.inl 1, Sum.inr (Sum.inr 1)] i
  | .inr (.inl i) => ![Sum.inr (Sum.inl (0 : Fin 2)), Sum.inr (Sum.inl 1), Sum.inr (Sum.inr 1)] i
  | .inr (.inr _) => Sum.inr (Sum.inr 0)

theorem a2lOddIdx_surjective : Function.Surjective a2lOddIdx := by
  decide

@[expose] noncomputable def a2lMinusToOdd : (quadMinus 3 F 0 1).Isometry (quadOdd 3 F) where
  toFun v := v ∘ a2lOddIdx
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_app' v := by
    rw [quadOdd_apply, quadMinus_apply]
    have h2 : ∀ g : Fin (3 - 1) → F, ∑ i, g i = g 0 + g 1 := Fin.sum_univ_two
    rw [h2, Fin.sum_univ_three]
    simp [a2lOddIdx]
    ring

theorem a2lMinusToOdd_injective : Function.Injective (a2lMinusToOdd F) :=
  Function.Surjective.injective_comp_right a2lOddIdx_surjective

theorem a2l_spinGroupMap_minusToOdd_injective [Finite F] (h2 : (2 : F) ≠ 0)
    (hirr : ∀ s : F, s ^ 2 + (0 : F) * s + 1 ≠ 0) :
    Function.Injective (a2lMinusToOdd F).spinGroupMap :=
  spinGroupMap_injective_of_injective h2 (nondegenerate_quadMinus_of_finite 3 F hirr) _
    (a2lMinusToOdd_injective F)

end MinusToOdd

section MinusToPlus

variable (F : Type) [Field F]

@[expose] def a2lPlusIdx : Fin 4 ⊕ Fin 4 → Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2
  | .inl i => ![Sum.inl (0 : Fin 2), Sum.inl 1, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1)] i
  | .inr i => ![Sum.inr (Sum.inl (0 : Fin 2)), Sum.inr (Sum.inl 1), Sum.inr (Sum.inr 0),
      Sum.inr (Sum.inr 1)] i

theorem a2lPlusIdx_surjective : Function.Surjective a2lPlusIdx := by
  decide

@[expose] noncomputable def a2lMinusToPlus : (quadMinus 3 F 0 1).Isometry (quadPlus 4 F) where
  toFun v := v ∘ a2lPlusIdx
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_app' v := by
    rw [quadPlus_apply, quadMinus_apply]
    have h2 : ∀ g : Fin (3 - 1) → F, ∑ i, g i = g 0 + g 1 := Fin.sum_univ_two
    rw [h2, Fin.sum_univ_four]
    simp [a2lPlusIdx]
    ring

theorem a2lMinusToPlus_injective : Function.Injective (a2lMinusToPlus F) :=
  Function.Surjective.injective_comp_right a2lPlusIdx_surjective

theorem a2l_spinGroupMap_minusToPlus_injective [Finite F] (h2 : (2 : F) ≠ 0)
    (hirr : ∀ s : F, s ^ 2 + (0 : F) * s + 1 ≠ 0) :
    Function.Injective (a2lMinusToPlus F).spinGroupMap :=
  spinGroupMap_injective_of_injective h2 (nondegenerate_quadMinus_of_finite 3 F hirr) _
    (a2lMinusToPlus_injective F)

end MinusToPlus

end CFSG.OddStandard.SmallF3.HypA2Leaves
