module

public import CFSG.LocalAnalysis.ComponentClassification.EvenOrthSelector
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddExc
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation

theorem oddLieCentralQuotient_of_semilinearRepresentation {J : Type} [Group J] {K : Type}
    [Field K] {d p : ℕ} {Q : QuadraticForm K (Fin d → K)} (hrep : SemilinearRepresentation Q)
    (ψ : J ≃* matrixProjectiveDerived Q)
    (h : ∀ g : similarityPairs Q, g.val.right ^ 2 = 1 →
      orderOf (matrixProjectiveConjugationHom Q g) = 2 →
      ∀ L : Subgroup (fixedSubgroup (matrixProjectiveConjugationHom Q g)), IsComponent L →
        OddLieCentralQuotient p L)
    (α : MulAut J) (hα : orderOf α = 2) {Kc : Subgroup (fixedSubgroup α)}
    (hKc : IsComponent Kc) : OddLieCentralQuotient p Kc := by
  set α' := MulAut.congr ψ α with hα'def
  have hα' : orderOf α' = 2 :=
    (orderOf_injective (MulAut.congr ψ).toMonoidHom (MulAut.congr ψ).injective α).trans hα
  have h2 : α' * α' = 1 := by
    have h2 := pow_orderOf_eq_one α'
    rw [hα'] at h2
    rw [← pow_two]
    exact h2
  have h1 : α' ≠ 1 := fun h => by
    rw [h, orderOf_one] at hα'
    exact absurd hα' (by norm_num)
  obtain ⟨β, g, hg, hσ2, -, -, -⟩ := hrep.2 α' h2 h1
  have hc : MulAut.congr β⁻¹ α' = β⁻¹ * α' * β := MulEquiv.ext fun _ => rfl
  have hord : orderOf (matrixProjectiveConjugationHom Q g) = 2 := by
    rw [← hg, ← hc]
    exact (orderOf_injective (MulAut.congr β⁻¹).toMonoidHom (MulAut.congr β⁻¹).injective
      α').trans hα'
  exact oddLieCentralQuotient_of_component_equiv ((fixedSubgroupCongrEquiv ψ α).trans
    (((fixedSubgroupCongrEquiv β⁻¹ α').trans
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hc))).trans
        (MulEquiv.subgroupCongr (congrArg fixedSubgroup hg)))) (h g hσ2 hord) hKc

@[expose] def OddOmegaPairConclusion {K : Type} [Field K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (p : ℕ) (g : similarityPairs Q) : Prop :=
  orderOf (matrixProjectiveConjugationHom Q g) = 2 →
    ∀ L : Subgroup (fixedSubgroup (matrixProjectiveConjugationHom Q g)), IsComponent L →
      OddLieCentralQuotient p L

@[expose] def OddOmegaOddLinearInput : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → Nat.card K = p ^ f →
    StatedLieAdmissible .POmegaOdd n p f → ∀ g : similarityPairs (coordinateQuadOdd n K),
      g.val.right = 1 → OddOmegaPairConclusion (coordinateQuadOdd n K) p g

@[expose] def OddOmegaPlusLinearInput : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → Nat.card K = p ^ f →
    StatedLieAdmissible .POmegaPlus n p f → ∀ g : similarityPairs (coordinateQuadPlus n K),
      g.val.right = 1 → OddOmegaPairConclusion (coordinateQuadPlus n K) p g

@[expose] def OddOmegaMinusLinearInput : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n) (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 →
    Nat.card K = p ^ f → StatedLieAdmissible .POmegaMinus n p f → ∀ b c : K,
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) → ∀ g : similarityPairs (coordinateQuadMinus n K hn b c),
        g.val.right = 1 → OddOmegaPairConclusion (coordinateQuadMinus n K hn b c) p g

@[expose] def OddOmegaOddFieldInput : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → Nat.card K = p ^ f →
    StatedLieAdmissible .POmegaOdd n p f → ∀ g : similarityPairs (coordinateQuadOdd n K),
      g.val.right ^ 2 = 1 → g.val.right ≠ 1 → OddOmegaPairConclusion (coordinateQuadOdd n K) p g

@[expose] def OddOmegaPlusFieldInput : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → Nat.card K = p ^ f →
    StatedLieAdmissible .POmegaPlus n p f → ∀ g : similarityPairs (coordinateQuadPlus n K),
      g.val.right ^ 2 = 1 → g.val.right ≠ 1 → OddOmegaPairConclusion (coordinateQuadPlus n K) p g

@[expose] def OddOmegaMinusFieldInput : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n) (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 →
    Nat.card K = p ^ f → StatedLieAdmissible .POmegaMinus n p f → ∀ b c : K,
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) → ∀ g : similarityPairs (coordinateQuadMinus n K hn b c),
        g.val.right ^ 2 = 1 → g.val.right ≠ 1 →
          OddOmegaPairConclusion (coordinateQuadMinus n K hn b c) p g

theorem gls3OddFamilyInput_POmegaOdd (hlin : OddOmegaOddLinearInput)
    (hfield : OddOmegaOddFieldInput) : GLS3OddFamilyInput .POmegaOdd := by
  intro J _ n p f hp hp2 hadm hm α hα Kc hKc
  refine Or.inl ?_
  have hC : StatedClassicalModel J .POmegaOdd n p f :=
    EvenOrthSelector.statedModel_of_lieModel (by decide) hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hC
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaOdd (Or.inl rfl)
    (EvenOrthSelector.statedModel_of_lieModel (by decide) hm) K hK e
  refine oddLieCentralQuotient_of_semilinearRepresentation hrep (coordinateOddWitnessEquiv K e)
    (fun g hσ2 hord L hL => ?_) α hα hKc
  by_cases hσ : g.val.right = 1
  · exact hlin n K p f hp hp2 hK hadm g hσ hord L hL
  · exact hfield n K p f hp hp2 hK hadm g hσ2 hσ hord L hL

theorem gls3OddFamilyInput_POmegaPlus (hlin : OddOmegaPlusLinearInput)
    (hfield : OddOmegaPlusFieldInput) : GLS3OddFamilyInput .POmegaPlus := by
  intro J _ n p f hp hp2 hadm hm α hα Kc hKc
  refine Or.inl ?_
  have hC : StatedClassicalModel J .POmegaPlus n p f :=
    EvenOrthSelector.statedModel_of_lieModel (by decide) hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hC
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaPlus
    (Or.inr (Or.inl rfl)) (EvenOrthSelector.statedModel_of_lieModel (by decide) hm) K hK e
  refine oddLieCentralQuotient_of_semilinearRepresentation hrep (coordinatePlusWitnessEquiv K e)
    (fun g hσ2 hord L hL => ?_) α hα hKc
  by_cases hσ : g.val.right = 1
  · exact hlin n K p f hp hp2 hK hadm g hσ hord L hL
  · exact hfield n K p f hp hp2 hK hadm g hσ2 hσ hord L hL

theorem gls3OddFamilyInput_POmegaMinus (hlin : OddOmegaMinusLinearInput)
    (hfield : OddOmegaMinusFieldInput) : GLS3OddFamilyInput .POmegaMinus := by
  intro J _ n p f hp hp2 hadm hm α hα Kc hKc
  refine Or.inl ?_
  have hC : StatedClassicalModel J .POmegaMinus n p f :=
    EvenOrthSelector.statedModel_of_lieModel (by decide) hm
  have hn : 1 ≤ n := by have := hadm.2.2; omega
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hC
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaMinus
    (Or.inr (Or.inr rfl)) (EvenOrthSelector.statedModel_of_lieModel (by decide) hm) hn K hK b c
    hirr e
  refine oddLieCentralQuotient_of_semilinearRepresentation hrep
    (coordinateMinusWitnessEquiv K hn b c e) (fun g hσ2 hord L hL => ?_) α hα hKc
  by_cases hσ : g.val.right = 1
  · exact hlin n hn K p f hp hp2 hK hadm b c hirr g hσ hord L hL
  · exact hfield n hn K p f hp hp2 hK hadm b c hirr g hσ2 hσ hord L hL

end CFSG.ComponentClassification.CatLeafProof
