module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaSmallMain
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPOmegaOrder
public import CFSG.LocalAnalysis.ComponentClassification.EvenOrthSelector

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation
open CFSG.ComponentClassification.CatFC.OmegaSmall

theorem card_orthogonalGroup_eq_card_matrixIsometries {K : Type} [Field K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = Nat.card (matrixIsometries Q) := by
  rw [← matrixIsometries_map Q]
  exact (Nat.card_congr ((matrixIsometries Q).equivMapOfInjective
    matrixLinearIso.toMonoidHom matrixLinearIso.injective).toEquiv).symm

theorem oddA6Small_POmegaOdd (hO : LieOrderFormulasInput) : OddA6Small .POmegaOdd := by
  refine oddA6Small_of_concrete fun S _ _ n p f hp hp2 hadm hm hp3 hs => ?_
  have hnf : n = 3 ∧ f = 1 := by
    rcases hs with h | h | h | h | h | h | h | h | h <;>
      first | exact absurd h.1 (by decide) | exact ⟨h.2.1, h.2.2⟩
  obtain ⟨rfl, rfl⟩ := hnf
  subst hp3
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
  refine ⟨matrixProjectiveDerived (coordinateQuadOdd 3 K), inferInstance, Finite.of_equiv S e', e',
    fun σ D hσ hD => ?_⟩
  have h1440 := omega_fixed_card_gt hK3 (d := 2 * 3 + 1) (Or.inl rfl) _ hQ hrep hcard σ hσ
  exact ⟨fun _ => h1440, fun _ h720 => absurd h720 (by omega)⟩

theorem oddA6Small_POmegaMinus (hO : LieOrderFormulasInput) : OddA6Small .POmegaMinus := by
  refine oddA6Small_of_concrete fun S _ _ n p f hp hp2 hadm hm hp3 hs => ?_
  have hnf : n = 4 ∧ f = 1 := by
    rcases hs with h | h | h | h | h | h | h | h | h <;>
      first | exact absurd h.1 (by decide) | exact ⟨h.2.1, h.2.2⟩
  obtain ⟨rfl, rfl⟩ := hnf
  subst hp3
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
  refine ⟨matrixProjectiveDerived (coordinateQuadMinus 4 K hn b c), inferInstance,
    Finite.of_equiv S e', e', fun σ D hσ hD => ?_⟩
  have h1440 := omega_fixed_card_gt hK3 (d := 2 * 4) (Or.inr rfl) _ hQ hrep hcard σ hσ
  exact ⟨fun _ => h1440, fun _ h720 => absurd h720 (by omega)⟩

end CFSG.ComponentClassification.CatFC
