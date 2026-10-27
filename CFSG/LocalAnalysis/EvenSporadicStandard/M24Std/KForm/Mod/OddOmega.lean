module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaSmall
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaXTwo

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation
open CFSG.ComponentClassification.CatFC
open CFSG.ComponentClassification.CatFC.OmegaSmall

theorem pomegaOdd_two_pow_six (hO : LieOrderFormulasInput) {S : Type} [Group S] [Finite S]
    (hadm : StatedLieAdmissible .POmegaOdd 3 3 1) (hm : LieModel S .POmegaOdd 3 3 1)
    {σ : MulAut S} (hσ : orderOf σ = 2) {D : Subgroup ↥(fixedSubgroup σ)} (hD : A6Hyp σ D) :
    2 ^ 6 ∣ Nat.card (fixedSubgroup σ) := by
  have hC : StatedClassicalModel S .POmegaOdd 3 3 1 :=
    EvenOrthSelector.statedModel_of_lieModel (by decide) hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hC
  have hK3 : Nat.card K = 3 := by simpa using hK
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaOdd (Or.inl rfl)
    (EvenOrthSelector.statedModel_of_lieModel (by decide) hm) K hK e
  obtain ⟨-, hQ, -⟩ := coordinate_model_witness_odd
    (EvenOrthSelector.statedModel_of_lieModel (by decide) hm) K hK e
  let e' := coordinateOddWitnessEquiv K e
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_card_three hK3)
  have hord := hO S .POmegaOdd 3 3 1 hadm hm
  have hmul : Nat.card S * 2 = lieOrderNumerator .POmegaOdd 3 3 := by
    simpa [lieOrderDivisor] using hord.2.1
  have hiso := HardMathSupport.Lang.UnitaryAutomorphisms.card_matrixIsometries_coordinateQuadOdd
    h2 3
  rw [hK3] at hiso
  have hcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadOdd 3 K)) =
      4 * Nat.card (matrixProjectiveDerived (coordinateQuadOdd 3 K)) := by
    rw [card_orthogonalGroup_eq_card_matrixIsometries, hiso, ← Nat.card_congr e'.toEquiv]
    omega
  haveI : Finite (matrixProjectiveDerived (coordinateQuadOdd 3 K)) := Finite.of_equiv S e'
  have h := omega_X_core_two hK3 (d := 2 * 3 + 1) (Or.inl rfl) _ hQ hrep hcard hO
    (MulAut.congr e' σ) ((orderOf_congr e' σ).trans hσ) (a6Hyp_congr e' σ D hD)
  rwa [← Nat.card_congr (fixedEquiv e' σ).toEquiv] at h

theorem pomegaMinus_two_pow_six (hO : LieOrderFormulasInput) {S : Type} [Group S] [Finite S]
    (hadm : StatedLieAdmissible .POmegaMinus 4 3 1) (hm : LieModel S .POmegaMinus 4 3 1)
    {σ : MulAut S} (hσ : orderOf σ = 2) {D : Subgroup ↥(fixedSubgroup σ)} (hD : A6Hyp σ D) :
    2 ^ 6 ∣ Nat.card (fixedSubgroup σ) := by
  have hC : StatedClassicalModel S .POmegaMinus 4 3 1 :=
    EvenOrthSelector.statedModel_of_lieModel (by decide) hm
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hC
  have hK3 : Nat.card K = 3 := by simpa using hK
  have hn : 1 ≤ 4 := by norm_num
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaMinus
    (Or.inr (Or.inr rfl)) (EvenOrthSelector.statedModel_of_lieModel (by decide) hm) hn K hK b c
    hirr e
  obtain ⟨-, hQ, -⟩ := coordinate_model_witness_minus
    (EvenOrthSelector.statedModel_of_lieModel (by decide) hm) K hK b c hirr e
  let e' := coordinateMinusWitnessEquiv K hn b c e
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_card_three hK3)
  have hord := hO S .POmegaMinus 4 3 1 hadm hm
  have hmul : Nat.card S * 2 = lieOrderNumerator .POmegaMinus 4 3 := by
    simpa [lieOrderDivisor] using hord.2.1
  have hiso :=
    HardMathSupport.Lang.UnitaryAutomorphisms.card_matrixIsometries_coordinateQuadMinus
      h2 4 hn hirr
  rw [hK3] at hiso
  have hcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      (coordinateQuadMinus 4 K hn b c)) =
      4 * Nat.card (matrixProjectiveDerived (coordinateQuadMinus 4 K hn b c)) := by
    rw [card_orthogonalGroup_eq_card_matrixIsometries, hiso, ← Nat.card_congr e'.toEquiv]
    omega
  haveI : Finite (matrixProjectiveDerived (coordinateQuadMinus 4 K hn b c)) :=
    Finite.of_equiv S e'
  have h := omega_X_core_two hK3 (d := 2 * 4) (Or.inr rfl) _ hQ hrep hcard hO
    (MulAut.congr e' σ) ((orderOf_congr e' σ).trans hσ) (a6Hyp_congr e' σ D hD)
  rwa [← Nat.card_congr (fixedEquiv e' σ).toEquiv] at h

end CFSG.EvenSporadicStandard.M24Std.KForm
