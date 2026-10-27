module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatTwoLayerC5OmegaE
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatDefs

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.TwoL5

open CFSG Subgroup CFSG.Open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation

namespace Omega

theorem litUnique_fixedSubgroup {S : Type} [Group S] {K : Type} [Field K] [Finite K]
    {d f n : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 5 ^ f)
    (hdim : d = 2 * n + 1 ∧ 3 ≤ n ∨ d = 2 * n ∧ 4 ≤ n) (Q : QuadraticForm K (Fin d → K))
    (hQ : Q.polarBilin.Nondegenerate) (hrep : SemilinearRepresentation Q)
    (ψ : S ≃* matrixProjectiveDerived Q) {σ : MulAut S} (hσσ : σ * σ = 1) (hσ1 : σ ≠ 1) :
    LitUnique ↥(fixedSubgroup σ) := by
  have hα2 : MulAut.congr ψ σ * MulAut.congr ψ σ = 1 := by rw [← map_mul, hσσ, map_one]
  have hα1 : MulAut.congr ψ σ ≠ 1 := fun h =>
    hσ1 ((MulAut.congr ψ).injective (h.trans (map_one _).symm))
  exact LitUnique.of_mulEquiv (Sporadic.HeldB.fixedSubgroupCongr ψ σ)
    (litUnique_involution hf hK hdim Q hQ hrep _ hα2 hα1)

theorem false_of_orth_data {S : Type} [Group S] [Finite S] [IsSimpleGroup S] {K : Type} [Field K]
    [Finite K] {d f n : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 5 ^ f)
    (hdim : d = 2 * n + 1 ∧ 3 ≤ n ∨ d = 2 * n ∧ 4 ≤ n) (Q : QuadraticForm K (Fin d → K))
    (hQ : Q.polarBilin.Nondegenerate) (hrep : SemilinearRepresentation Q)
    (ψ : S ≃* matrixProjectiveDerived Q) {σ : MulAut S} {P₁ P₂ : Subgroup S}
    (h₁ : ProperFixedComponent σ P₁) (h₂ : ProperFixedComponent σ P₂) (hne : P₁ ≠ P₂)
    (hZ₁ : Open.fusionZStar ↥P₁ = pPrimeCore 2 ↥P₁)
    (hZ₂ : Open.fusionZStar ↥P₂ = pPrimeCore 2 ↥P₂)
    (e₁ : Nonempty (↥P₁ ⧸ Open.fusionZStar ↥P₁ ≃* alternatingGroup (Fin 5)))
    (e₂ : Nonempty (↥P₂ ⧸ Open.fusionZStar ↥P₂ ≃* alternatingGroup (Fin 5)))
    (huniq : ∀ P' : Subgroup S, ProperFixedComponent σ P' → P' = P₁ ∨ P' = P₂) : False := by
  have hq : ∀ α : MulAut S, α * α = 1 → α ≠ 1 →
      ∀ L : Subgroup (fixedSubgroup α), IsPComponent 2 L → IsQuasisimple L := by
    intro α hα2 hα1 L hL
    have hα2' : MulAut.congr ψ α * MulAut.congr ψ α = 1 := by rw [← map_mul, hα2, map_one]
    have hα1' : MulAut.congr ψ α ≠ 1 := fun h =>
      hα1 ((MulAut.congr ψ).injective (h.trans (map_one _).symm))
    exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv 2
      (Sporadic.HeldB.fixedSubgroupCongr ψ α)
      ((CatalogueBOrthogonalInvolutionFixedComponents.fixed_pComponent_quasisimple_of_representation
        5 f Nat.prime_five (by norm_num) hf hK (by omega) Q hQ hrep _ hα2' hα1') 2 Nat.prime_two)
      L hL
  have hσ1 : σ ≠ 1 := h₁.ne_one
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h₁.1 y
  have hT : TwoLayers (fixedSubgroup σ) := twoLayers_of_clause hq h₁ h₂ hne hZ₁ hZ₂ e₁ e₂ huniq
  exact (litUnique_fixedSubgroup hf hK hdim Q hQ hrep ψ hσσ hσ1).not_twoLayers hT

end Omega

theorem fiveTwoLayer_char5_POmegaOdd : FiveTwoLayerCharFiveClause .POmegaOdd := by
  intro S _ _ hs _hna ⟨n, f, hm⟩ σ P₁ P₂ h₁ h₂ hne hZ₁ hZ₂ e₁ e₂ huniq
  exfalso
  have hadm : StatedLieAdmissible .POmegaOdd n 5 f := hm.admissible
  have hC : StatedClassicalModel S .POmegaOdd n 5 f := hm.statedClassicalModel (by decide)
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hC
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaOdd (Or.inl rfl) hC K hK
    e
  obtain ⟨-, hQ, -⟩ := coordinate_model_witness_odd hC K hK e
  exact Omega.false_of_orth_data hadm.2.1 hK (Or.inl ⟨rfl, hadm.2.2.1⟩) (coordinateQuadOdd n K) hQ
    hrep (coordinateOddWitnessEquiv K e) h₁ h₂ hne hZ₁ hZ₂ e₁ e₂ huniq

theorem fiveTwoLayer_char5_POmegaPlus : FiveTwoLayerCharFiveClause .POmegaPlus := by
  intro S _ _ hs _hna ⟨n, f, hm⟩ σ P₁ P₂ h₁ h₂ hne hZ₁ hZ₂ e₁ e₂ huniq
  exfalso
  have hadm : StatedLieAdmissible .POmegaPlus n 5 f := hm.admissible
  have hC : StatedClassicalModel S .POmegaPlus n 5 f := hm.statedClassicalModel (by decide)
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hC
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaPlus
    (Or.inr (Or.inl rfl)) hC K hK e
  obtain ⟨-, hQ, -⟩ := coordinate_model_witness_plus hC K hK e
  exact Omega.false_of_orth_data hadm.2.1 hK (Or.inr ⟨rfl, hadm.2.2⟩) (coordinateQuadPlus n K) hQ
    hrep (coordinatePlusWitnessEquiv K e) h₁ h₂ hne hZ₁ hZ₂ e₁ e₂ huniq

theorem fiveTwoLayer_char5_POmegaMinus : FiveTwoLayerCharFiveClause .POmegaMinus := by
  intro S _ _ hs _hna ⟨n, f, hm⟩ σ P₁ P₂ h₁ h₂ hne hZ₁ hZ₂ e₁ e₂ huniq
  exfalso
  have hadm : StatedLieAdmissible .POmegaMinus n 5 f := hm.admissible
  have hn : 1 ≤ n := by have := hadm.2.2; omega
  have hC : StatedClassicalModel S .POmegaMinus n 5 f := hm.statedClassicalModel (by decide)
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := id hC
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaMinus
    (Or.inr (Or.inr rfl)) hC hn K hK b c hirr e
  obtain ⟨-, hQ, -⟩ := coordinate_model_witness_minus hC K hK b c hirr e
  exact Omega.false_of_orth_data hadm.2.1 hK (Or.inr ⟨rfl, hadm.2.2⟩)
    (coordinateQuadMinus n K hn b c) hQ hrep (coordinateMinusWitnessEquiv K hn b c e) h₁ h₂ hne
    hZ₁ hZ₂ e₁ e₂ huniq

end CFSG.ComponentClassification.SolMax.FiveCat.TwoL5
