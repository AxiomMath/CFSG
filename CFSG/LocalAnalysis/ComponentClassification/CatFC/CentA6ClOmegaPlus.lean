module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaLin
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaField
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Transport
public import CFSG.LocalAnalysis.ComponentClassification.EvenOrthSelector

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Module
open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof (GLS3OddFamilyInput)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed (projectiveDerived)
open CFSG.GroupTheory.WeirSylow (IsPlusType isPlusType_congr isPlusType_quadPlus)

theorem omegaPlus_isPlusType (n : ℕ) (K : Type) [Field K] :
    IsPlusType (coordinateQuadPlus n K) :=
  (isPlusType_congr (coordinatePlusIsometry n K)).1 (isPlusType_quadPlus K n)

theorem omegaPlus_a6Hyp_of_eq {S : Type} [Group S] {σ σ' : MulAut S} (h : σ = σ')
    {D : Subgroup ↥(fixedSubgroup σ)} (hD : A6Hyp σ D) :
    ∃ D' : Subgroup ↥(fixedSubgroup σ'), A6Hyp σ' D' := by
  subst h
  exact ⟨D, hD⟩

theorem omegaPlus_false
    {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 3 ^ f) (hO : LieOrderFormulasInput)
    (hrep : SemilinearRepresentation (coordinateQuadPlus n K))
    {σ : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))} (hσ : orderOf σ = 2)
    {D : Subgroup ↥(fixedSubgroup σ)} (hD : A6Hyp σ D) : False := by
  have hQ := (regular_coordinateQuadPlus n K (by omega : 3 ≤ n)).1
  have h2 : σ * σ = 1 := by
    have h := pow_orderOf_eq_one σ
    rw [hσ, pow_two] at h
    exact h
  have h1 : σ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  obtain ⟨β, g, hg, hσ2, ⟨c, hc⟩, hnsc, -⟩ := hrep.2 σ h2 h1
  have hconj : MulAut.congr β⁻¹ σ = matrixProjectiveConjugationHom (coordinateQuadPlus n K) g :=
    (MulEquiv.ext fun _ => rfl : MulAut.congr β⁻¹ σ = β⁻¹ * σ * β).trans hg
  obtain ⟨D₂, hD₂⟩ := omegaPlus_a6Hyp_of_eq hconj (a6Hyp_congr β⁻¹ σ D hD)
  by_cases hg1 : g.val.right = 1
  ·
    have hQ0 : ∃ v, coordinateQuadPlus n K v ≠ 0 :=
      exists_ne_zero_of_polarBilin_nondegenerate _ hQ (by omega)
    have hsim := matrix_similarity (coordinateQuadPlus n K) g hg1
    have hsq : ∀ x, matrixLinearEquiv g.val.left (matrixLinearEquiv g.val.left x) =
        (c : K) • x := by
      intro x
      have h := coordinateSemilinearMap_sq_apply g.val c (by rw [hg1, one_pow]) hc x
      rwa [coordinateSemilinearMap_eq_matrix g.val hg1] at h
    obtain ⟨D₃, hD₃⟩ := omegaPlus_a6Hyp_of_eq (mulAutCongr_conjugation_linear _ hQ0 g hg1)
      (a6Hyp_congr (projectiveEquiv _ hQ0) _ D₂ hD₂)
    have : Finite (projectiveDerived (coordinateQuadPlus n K)) :=
      Finite.of_equiv _ (projectiveEquiv _ hQ0).toEquiv
    obtain ⟨-, hdim⟩ := omega_linear_core hf hK hO (coordinateQuadPlus n K) hQ
      (matrixLinearEquiv g.val.left) c (multiplier (coordinateQuadPlus n K) g) hsq hsim
      (matrixLinearEquiv_ne_smul_one g.val.left (hnsc hg1))
      (by rw [Module.finrank_fin_fun]; omega) hD₃
    rw [Module.finrank_fin_fun] at hdim
    rcases hdim with h7 | ⟨h8, hnp⟩
    · omega
    · exact hnp (omegaPlus_isPlusType n K)
  ·
    obtain ⟨hDc, hDA⟩ := hD₂.component
    exact omega_field_false Nat.prime_three (by norm_num) hf hK (Or.inr ⟨rfl, hn⟩) hQ g hσ2 hg1 c
      hc hO hDc hDA

theorem oddA6Shape_POmegaPlus
    (hO : LieOrderFormulasInput) (hgls : GLS3OddFamilyInput .POmegaPlus) :
    OddA6Shape .POmegaPlus := by
  apply oddA6Shape_of_concrete
  intro S _ _ n p f hp hp2 hadm hm
  have hC : StatedClassicalModel S .POmegaPlus n p f :=
    EvenOrthSelector.statedModel_of_lieModel (by decide) hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hC
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaPlus
    (Or.inr (Or.inl rfl)) (EvenOrthSelector.statedModel_of_lieModel (by decide) hm) K hK e
  let ψ := coordinatePlusWitnessEquiv K e
  refine ⟨matrixProjectiveDerived (coordinateQuadPlus n K), inferInstance,
    Finite.of_equiv S ψ.toEquiv, ψ, ?_⟩
  intro σ D hσ hD
  exfalso
  have hmX : LieModel (matrixProjectiveDerived (coordinateQuadPlus n K)) .POmegaPlus n p f :=
    Blueprint.LieModel.of_mulEquiv ψ hm
  have hp3 : p = 3 := hD.char_three hO hgls hp hp2 hadm hmX hσ
  subst hp3
  exact omegaPlus_false hadm.2.2 hadm.2.1 hK hO hrep hσ hD

end CFSG.ComponentClassification.CatFC
