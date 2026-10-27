module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBStated
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBSymplecticB

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher CatalogueBSymplecticRepresentation

theorem odd_symplectic_involution_fixed_p_components (ℓ f : ℕ) (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) (r : ℕ) (hr : 2 ≤ r)
    (α : MulAut (StatedProj (StatedSp r K))) (h2 : α * α = 1) (h1 : α ≠ 1) :
    ∀ p : ℕ, p.Prime → ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup α),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L := by
  intro p hp L hL
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have hchar : ringChar K ≠ 2 := by
    rw [ringChar.eq K ℓ]
    exact hodd
  have hr1 : 1 ≤ r := by omega
  have hdim : Module.finrank K (Fin r ⊕ Fin r → K) = 2 * r := SymplecticFlag.finrank_standard
  obtain ⟨A, σ, hα, hσ2, ⟨d, hd⟩, hlin, -⟩ :=
    (odd_symplectic_automorphism_semilinear_representation hchar hr).2.2 α h2 h1
  set μ := multiplierUnit A with hμdef
  have hμ := multiplierUnit_spec A
  let e := projectiveStatedEquiv (K := K) hr1
  by_cases hσ : σ = 1
  · subst hσ
    have hint : ∀ x, e (α x) = projectiveConjugation (pairedSympForm K r)
        (matrixLinIso (A : GL (Fin r ⊕ Fin r) K)) μ (matrix_similitude _ μ hμ) (e x) := by
      intro x
      rw [hα, map_one, mul_one]
      exact projectiveStatedEquiv_conjAut hr1 A μ hμ x
    have hsquare : ∀ x, matrixLinIso (A : GL (Fin r ⊕ Fin r) K)
        (matrixLinIso (A : GL (Fin r ⊕ Fin r) K) x) = (d : K) • x :=
      semilinearCoordMap_sq _ 1 hσ2 d hd
    exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv p
      (CatalogueBOrthogonalFixedTransfer.fixedEquivOfIntertwining e α _ hint)
      ((odd_symplectic_linear_involution_fixed_p_components ℓ f hℓ hodd hf hK r hr1 hdim
        (pairedSympForm K r) SymplecticFlag.pairedSympForm_isAlt
        SymplecticFlag.pairedSympForm_nondegenerate (matrixLinIso (A : GL (Fin r ⊕ Fin r) K))
        d μ hsquare (matrix_similitude _ μ hμ)
        (matrixLinIso_ne_smul_one _ (hlin rfl))).2 p hp) L hL
  · have hint : ∀ x, e (α x) = projectiveSemilinearConjugation (pairedSympForm K r) σ
        (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) K) σ) μ (semilinearCoordMap_smul _ σ)
        (semilinearCoordMap_form _ σ μ hμ) (e x) := by
      intro x
      rw [hα]
      exact projectiveStatedEquiv_conjAut_fieldAut hr1 A σ μ hμ x
    have hKodd : Odd (Nat.card K) := by
      rw [hK]
      exact (hℓ.odd_of_ne_two hodd).pow
    exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv p
      (CatalogueBOrthogonalFixedTransfer.fixedEquivOfIntertwining e α _ hint)
      ((odd_symplectic_field_involution_fixed_p_components hKodd σ hσ2 hσ (by omega)
        (pairedSympForm K r) SymplecticFlag.pairedSympForm_isAlt
        SymplecticFlag.pairedSympForm_nondegenerate
        (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) K) σ) μ d (semilinearCoordMap_smul _ σ)
        (semilinearCoordMap_form _ σ μ hμ) (semilinearCoordMap_sq _ σ hσ2 d hd)).2 p hp) L hL

end CFSG.ComponentClassification.CatalogueBSymplecticB
