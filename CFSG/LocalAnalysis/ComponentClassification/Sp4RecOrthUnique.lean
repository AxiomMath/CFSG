module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalLinearFixedBranches
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.ComponentClassification.Sp4Rec

open CFSG Subgroup Module
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms
  CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem linEquiv_pComponent_eq {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (hW : 1 ≤ finrank K W) {J₁ J₂ : Subgroup (W ≃ₗ[K] W)} (h₁ : IsPComponent 2 J₁)
    (h₂ : IsPComponent 2 J₂) : J₁ = J₂ := by
  set e := CatalogueBAlternatingIsometry.basisMatrixEquiv (Module.finBasis K W)
  obtain ⟨-, -, -, k₁, -⟩ := CatalogueBGeneralLinear.pComponent_classification _ K hW 2 _
    (CatalogueBAlternating.pComponent_map_equiv 2 e _ h₁)
  obtain ⟨-, -, -, k₂, -⟩ := CatalogueBGeneralLinear.pComponent_classification _ K hW 2 _
    (CatalogueBAlternating.pComponent_map_equiv 2 e _ h₂)
  exact map_injective e.injective (k₁.trans k₂.symm)

theorem orth_negative_nonsquare_pComponent_eq [Nontrivial V] (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (T : Module.End K V) (d : K) (hd : d ≠ 0) (hns : ¬ IsSquare d)
    (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (hadj : ∀ x y, Q.polarBilin (T x) y = -Q.polarBilin x (T y)) (hdim : 6 ≤ finrank K V)
    {L₁ L₂ : Subgroup (orthogonalOperatorCentralizer Q T)} (h₁ : IsPComponent 2 L₁)
    (h₂ : IsPComponent 2 L₂) : L₁ = L₂ := by
  let := scalarField T d hns hsquare
  let := evaluationModule T
  let := scalarAlgebra_finite_type T d hns hsquare
  let := evaluationModule_finite T
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  let h := actualNegativeHermitian Q.polarBilin T d hd hns hsquare hadj
  have hsig : (conjugation T d hns hsquare).toRingEquiv ^ 2 = 1 := by
    apply RingEquiv.ext
    intro z
    change conjugation T d hns hsquare (conjugation T d hns hsquare z) = z
    exact conjugation_involutive T d hns hsquare z
  have hne : (conjugation T d hns hsquare).toRingEquiv ≠ 1 := by
    intro heq
    apply conjugation_ne_one T d hns hsquare h2
    apply AlgEquiv.ext
    intro z
    exact congrArg (fun s : scalarAlgebra T ≃+* scalarAlgebra T => s z) heq
  have hq2 : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield (scalarAlgebra T)
      (conjugation T d hns hsquare).toRingEquiv) ≠ 2 := by
    rw [scalarFixedField_card T d hns hsquare h2]
    intro hc2
    have hh := hodd
    rw [hc2] at hh
    norm_num at hh
  have hfin := evaluationModule_finrank T d hns hsquare
  set e := actualNegativeCentralizerEquiv Q T d hd hns hsquare hadj h2
  have hall := (CatalogueBUnitaryIsometry.isometry_all_dimensions_nonsmall h
    (actualNegativeHermitian_isSymm Q T d hd hns hsquare hadj)
    (actualNegativeHermitian_nondegenerate Q T d hd hns hsquare hadj hQ) hsig hne
    (by omega) hq2 (by omega) (fun hpq => by
      have := congrArg Prod.fst hpq
      simp only at this
      omega)).2 2 Nat.prime_two
  have e₁ := (hall _ (CatalogueBAlternating.pComponent_map_equiv 2 e _ h₁)).1
  have e₂ := (hall _ (CatalogueBAlternating.pComponent_map_equiv 2 e _ h₂)).1
  exact map_injective e.injective (e₁.trans e₂.symm)

end CFSG.ComponentClassification.Sp4Rec
