module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.BT2Basic
public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Orthogonal

public noncomputable section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open QuadraticMap Matrix Module CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.ComponentClassification.UnbalancingLocal.EvenOrthogonalComponents
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  (orthogonal_geometry_char_two_reflection_separation)

variable {K : Type} [Field K] {d : ℕ}

section Regular

variable [Finite K] [CharP K 2] {Q : QuadraticForm K (Fin d → K)}
  (hQ : Q.polarBilin.Nondegenerate)
  (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
  (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
    elementaryGroup Q)

include hQ hT hE in
theorem involutionCentralizersCharTwo_matrixProjectiveDerived :
    InvolutionCentralizersCharTwo (matrixProjectiveDerived Q) := by
  intro x hx
  have : Finite (matrixProjectiveDerived Q) := by
    have : Finite (GL (Fin d) K) := inferInstance
    infer_instance
  have hconj := conj_injective_matrixProjectiveDerived hQ hT hE
  obtain ⟨g, rfl⟩ := matrixProjectiveProjection_surjective Q x
  have hα : MulAut.conj (matrixProjectiveProjection Q g) =
      matrixProjectiveConjugationHom Q
        (matrixIsometryInclusion Q (Subgroup.inclusion (matrixDerived_le_isometries Q) g)) :=
    (matrixProjectiveConjugationHom_derived Q g).symm
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hx
    omega
  have hg2 : g * g = 1 := by
    apply derivedKappa_injective hQ hT hE
    rw [map_mul, map_one, derivedKappa, MonoidHom.comp_apply,
      matrixProjectiveConjugationHom_derived, ← map_mul, ← pow_two, ← hx, pow_orderOf_eq_one,
      map_one]
  have hrank := two_le_rank_of_mem_derived hQ hT hE g hg1 hg2
  obtain ⟨R, hRX, hnorm, hR, hcent⟩ := exists_two_radical_of_two_le_rank hQ hT hE
    (CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q)) le_rfl
    (by
      rintro _ ⟨y, rfl⟩
      obtain ⟨h, rfl⟩ := matrixProjectiveProjection_surjective Q y
      exact ⟨_, matrixProjectiveConjugationHom_derived Q h⟩)
    (Subgroup.inclusion (matrixDerived_le_isometries Q) g)
    (by rw [← hα, orderOf_injective _ hconj]; exact hx) hrank
  rw [← hα] at hRX hnorm hcent
  exact isCharacteristicP_two_centralizer_of_two_radical
    (MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)) hconj R hRX
    hnorm hR hcent

end Regular

theorem involutionCentralizersCharTwo_of_pOmega_model {T : Type} [Group T] {t : StatedLieTag}
    {n f : ℕ} (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (hT : StatedClassicalModel T t n 2 f) :
    InvolutionCentralizersCharTwo T := by
  obtain ⟨-, hf, hn⟩ := hT.1
  rcases ht with rfl | rfl
  · obtain ⟨-, K, _, _, hK, ⟨eT⟩⟩ := hT
    have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hf hK
    have hreg := regular_coordinateQuadPlus n K (by omega)
    have hcomm := commutator_coordinateQuadPlus n K (by omega)
    exact InvolutionCentralizersCharTwo.of_mulEquiv (coordinatePlusWitnessEquiv K eT)
      (involutionCentralizersCharTwo_matrixProjectiveDerived hreg.1 hreg.2 hcomm)
  · obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨eT⟩⟩ := hT
    have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hf hK
    have hreg := regular_coordinateQuadMinus n K b c hn hirr
    have hcomm := commutator_coordinateQuadMinus n K b c hn hirr
    exact InvolutionCentralizersCharTwo.of_mulEquiv
      (coordinateMinusWitnessEquiv K (by omega) b c eT)
      (involutionCentralizersCharTwo_matrixProjectiveDerived hreg.1 hreg.2 hcomm)


end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
