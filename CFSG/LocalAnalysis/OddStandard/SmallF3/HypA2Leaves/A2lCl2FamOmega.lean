module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamCore
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamOInner
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamOField
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamOrth
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOmega
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSp
public import CFSG.LocalAnalysis.ComponentClassification.EvenOrthSelector
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerOmega
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerOLift
public import CFSG.RankThree.Classical.SteinbergBYOrthogonalGates
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOmegaField
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOmegaForms
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFieldFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOrthAll

public noncomputable section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG
  CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification
open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation

@[expose] def Cl24OmegaPair {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K)) (p : ℕ)
    (R : ℕ → Prop) (g : similarityPairs Q) : Prop :=
  orderOf (matrixProjectiveConjugationHom Q g) = 2 →
    ∀ L : Subgroup (fixedSubgroup (matrixProjectiveConjugationHom Q g)), IsComponent L →
      Cl24Q p R L

theorem cl24_of_semilinearRepresentation {J : Type} [Group J] {K : Type}
    [Field K] {d p : ℕ} {R : ℕ → Prop} {Q : QuadraticForm K (Fin d → K)}
      (hrep : SemilinearRepresentation Q)
    (ψ : J ≃* matrixProjectiveDerived Q)
    (h : ∀ g : similarityPairs Q, g.val.right ^ 2 = 1 →
      orderOf (matrixProjectiveConjugationHom Q g) = 2 →
      ∀ L : Subgroup (fixedSubgroup (matrixProjectiveConjugationHom Q g)), IsComponent L →
        Cl24Q p R L)
    (α : MulAut J) (hα : orderOf α = 2) {Kc : Subgroup (fixedSubgroup α)}
    (hKc : IsComponent Kc) : Cl24Q p R Kc := by
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
  exact cl24_of_component_equiv ((fixedSubgroupCongrEquiv ψ α).trans
    (((fixedSubgroupCongrEquiv β⁻¹ α').trans
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hc))).trans
        (MulEquiv.subgroupCongr (congrArg fixedSubgroup hg)))) (h g hσ2 hord) hKc

theorem cl24_omegaOdd_linear :
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → Nat.card K = p ^ f →
    StatedLieAdmissible .POmegaOdd n p f → ∀ g : similarityPairs (coordinateQuadOdd n K),
      g.val.right = 1 → Cl24OmegaPair (coordinateQuadOdd n K) p (Cl24FieldRel f) g := by
  intro n K _ _ p f hp hp2 hK hadm g hg hord L hL
  have hstated : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadOdd n K))) .POmegaOdd
      n p f := ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨-, hnd, hT, -, hAP, -⟩ := coordinate_model_witness_odd hstated K hK (MulEquiv.refl _)
  exact cl24_oddLie_inner_omega (cl24_orthogonalComponentsLie_holds hp hp2) hp hp2 hadm.2.1 hK
    (by omega) hnd
    (RankThree.Classical.SteinbergBY.matrixProjectiveConjugationHom_eq_one_iff _ hnd hT hAP) g
    hg hord hL

theorem cl24_omegaPlus_linear :
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → Nat.card K = p ^ f →
    StatedLieAdmissible .POmegaPlus n p f → ∀ g : similarityPairs (coordinateQuadPlus n K),
      g.val.right = 1 → Cl24OmegaPair (coordinateQuadPlus n K) p
        (fun f' => f' = f ∨ f' = 2 * f ∨ (n = 4 ∧ f' = 4 * f) ∨ f = 2 * f') g := by
  intro n K _ _ p f hp hp2 hK hadm g hg hord L hL
  have hstated : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus n K))) .POmegaPlus
      n p f := ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨-, hnd, hT, -, hAP, -⟩ := coordinate_model_witness_plus hstated K hK (MulEquiv.refl _)
  have hn : 4 ≤ n := hadm.2.2
  exact cl24_oddLie_inner_omega (cl24_orthogonalComponentsLie_holds hp hp2) hp hp2 hadm.2.1 hK
    (by omega) hnd
    (RankThree.Classical.SteinbergBY.matrixProjectiveConjugationHom_eq_one_iff _ hnd hT hAP) g
    hg hord hL

theorem cl24_omegaMinus_linear :
  ∀ (n : ℕ) (hn : 1 ≤ n) (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 →
    Nat.card K = p ^ f → StatedLieAdmissible .POmegaMinus n p f → ∀ b c : K,
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) → ∀ g : similarityPairs (coordinateQuadMinus n K hn b c),
        g.val.right = 1 → Cl24OmegaPair (coordinateQuadMinus n K hn b c) p (Cl24FieldRel f) g := by
  intro n hn K _ _ p f hp hp2 hK hadm b c hirr g hg hord L hL
  have hstated : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadMinus n K b c)))
      .POmegaMinus n p f := ⟨hadm, K, inferInstance, inferInstance, hK, b, c, hirr,
        ⟨MulEquiv.refl _⟩⟩
  obtain ⟨-, hnd, hT, -, hAP, -⟩ :=
    coordinate_model_witness_minus hstated K hK b c hirr (MulEquiv.refl _)
  exact cl24_oddLie_inner_omega (cl24_orthogonalComponentsLie_holds hp hp2) hp hp2 hadm.2.1 hK
    (by omega) hnd
    (RankThree.Classical.SteinbergBY.matrixProjectiveConjugationHom_eq_one_iff _ hnd hT hAP) g
    hg hord hL

theorem cl24_omegaOdd_field :
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → Nat.card K = p ^ f →
    StatedLieAdmissible .POmegaOdd n p f → ∀ g : similarityPairs (coordinateQuadOdd n K),
      g.val.right ^ 2 = 1 → g.val.right ≠ 1 → Cl24OmegaPair (coordinateQuadOdd n K) p
        (Cl24FieldRel f) g := by
  intro n K _ _ p f hp hp2 hK hadm g hσ2 hσ hord L hL
  have hstated : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadOdd n K))) .POmegaOdd
      n p f := ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨-, hnd, hT, -, hAP, -⟩ := coordinate_model_witness_odd hstated K hK (MulEquiv.refl _)
  obtain ⟨c, hc⟩ := exists_twisted_square_scalar (fun g' h =>
    (RankThree.Classical.SteinbergBY.matrixProjectiveConjugationHom_eq_one_iff _ hnd hT hAP
      g').mp h) g hord
  exact cl24_odd_omega_field_oddLieCentralQuotient hp hp2 hadm.2.1 hK (Or.inl ⟨rfl, hadm.2.2.1⟩) hnd
    g hσ2 hσ c hc hL

theorem cl24_omegaPlus_field :
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → Nat.card K = p ^ f →
    StatedLieAdmissible .POmegaPlus n p f → ∀ g : similarityPairs (coordinateQuadPlus n K),
      g.val.right ^ 2 = 1 → g.val.right ≠ 1 → Cl24OmegaPair (coordinateQuadPlus n K) p
        (fun f' => f' = f ∨ f' = 2 * f ∨ (n = 4 ∧ f' = 4 * f) ∨ f = 2 * f') g := by
  intro n K _ _ p f hp hp2 hK hadm g hσ2 hσ hord L hL
  have hstated : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus n K))) .POmegaPlus
      n p f := ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨-, hnd, hT, -, hAP, -⟩ := coordinate_model_witness_plus hstated K hK (MulEquiv.refl _)
  obtain ⟨c, hc⟩ := exists_twisted_square_scalar (fun g' h =>
    (RankThree.Classical.SteinbergBY.matrixProjectiveConjugationHom_eq_one_iff _ hnd hT hAP
      g').mp h) g hord
  exact cl24_odd_omega_field_oddLieCentralQuotient hp hp2 hadm.2.1 hK (Or.inr ⟨rfl, hadm.2.2⟩) hnd
    g hσ2 hσ c hc hL

theorem cl24_omegaMinus_field :
  ∀ (n : ℕ) (hn : 1 ≤ n) (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 →
    Nat.card K = p ^ f → StatedLieAdmissible .POmegaMinus n p f → ∀ b c : K,
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) → ∀ g : similarityPairs (coordinateQuadMinus n K hn b c),
        g.val.right ^ 2 = 1 → g.val.right ≠ 1 →
          Cl24OmegaPair (coordinateQuadMinus n K hn b c) p (Cl24FieldRel f) g := by
  intro n hn K _ _ p f hp hp2 hK hadm b c hirr g hσ2 hσ hord L hL
  have hstated : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadMinus n K b c)))
      .POmegaMinus n p f := ⟨hadm, K, inferInstance, inferInstance, hK, b, c, hirr,
        ⟨MulEquiv.refl _⟩⟩
  obtain ⟨-, hnd, hT, -, hAP, -⟩ :=
    coordinate_model_witness_minus hstated K hK b c hirr (MulEquiv.refl _)
  obtain ⟨c₀, hc₀⟩ := exists_twisted_square_scalar (fun g' h =>
    (RankThree.Classical.SteinbergBY.matrixProjectiveConjugationHom_eq_one_iff _ hnd hT hAP
      g').mp h) g hord
  exact cl24_odd_omega_field_oddLieCentralQuotient hp hp2 hadm.2.1 hK (Or.inr ⟨rfl, hadm.2.2⟩) hnd
    g hσ2 hσ c₀ hc₀ hL

theorem cl24_family_POmegaOdd : Cl24OddFamily .POmegaOdd := by
  intro J _ n p f hp hp2 hadm hm α hα Kc hKc
  refine Or.inl ?_
  have hC : StatedClassicalModel J .POmegaOdd n p f :=
    EvenOrthSelector.statedModel_of_lieModel (by decide) hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hC
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaOdd (Or.inl rfl)
    (EvenOrthSelector.statedModel_of_lieModel (by decide) hm) K hK e
  refine cl24_of_semilinearRepresentation hrep (coordinateOddWitnessEquiv K e)
    (fun g hσ2 hord L hL => ?_) α hα hKc
  by_cases hσ : g.val.right = 1
  · exact cl24_omegaOdd_linear n K p f hp hp2 hK hadm g hσ hord L hL
  · exact cl24_omegaOdd_field n K p f hp hp2 hK hadm g hσ2 hσ hord L hL

theorem cl24_omegaPlus_involution {J : Type} [Group J] {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .POmegaPlus n p f) (hm : Blueprint.LieModel J .POmegaPlus n p f)
    {α : MulAut J} (hα : orderOf α = 2) {Kc : Subgroup (fixedSubgroup α)}
    (hKc : IsComponent Kc) :
    Cl24Q p (fun f' => f' = f ∨ f' = 2 * f ∨ (n = 4 ∧ f' = 4 * f) ∨ f = 2 * f') Kc := by
  have hC : StatedClassicalModel J .POmegaPlus n p f :=
    EvenOrthSelector.statedModel_of_lieModel (by decide) hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hC
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaPlus
    (Or.inr (Or.inl rfl)) (EvenOrthSelector.statedModel_of_lieModel (by decide) hm) K hK e
  refine cl24_of_semilinearRepresentation hrep (coordinatePlusWitnessEquiv K e)
    (fun g hσ2 hord L hL => ?_) α hα hKc
  by_cases hσ : g.val.right = 1
  · exact cl24_omegaPlus_linear n K p f hp hp2 hK hadm g hσ hord L hL
  · exact cl24_omegaPlus_field n K p f hp hp2 hK hadm g hσ2 hσ hord L hL

theorem cl24_family_POmegaPlus : Cl24OddFamily .POmegaPlus := by
  intro J _ n p f hp hp2 hadm hm α hα Kc hKc
  refine Or.inl ((cl24_omegaPlus_involution hp hp2 hadm hm hα hKc).mono ?_)
  intro f' h
  unfold Cl24FieldRel
  omega

theorem cl24_family_POmegaMinus : Cl24OddFamily .POmegaMinus := by
  intro J _ n p f hp hp2 hadm hm α hα Kc hKc
  refine Or.inl ?_
  have hC : StatedClassicalModel J .POmegaMinus n p f :=
    EvenOrthSelector.statedModel_of_lieModel (by decide) hm
  have hn : 1 ≤ n := by have := hadm.2.2; omega
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hC
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaMinus
    (Or.inr (Or.inr rfl)) (EvenOrthSelector.statedModel_of_lieModel (by decide) hm) hn K hK b c
    hirr e
  refine cl24_of_semilinearRepresentation hrep
    (coordinateMinusWitnessEquiv K hn b c e) (fun g hσ2 hord L hL => ?_) α hα hKc
  by_cases hσ : g.val.right = 1
  · exact cl24_omegaMinus_linear n hn K p f hp hp2 hK hadm b c hirr g hσ hord L hL
  · exact cl24_omegaMinus_field n hn K p f hp hp2 hK hadm b c hirr g hσ2 hσ hord L hL

end CFSG.OddStandard.SmallF3.HypA2Leaves
