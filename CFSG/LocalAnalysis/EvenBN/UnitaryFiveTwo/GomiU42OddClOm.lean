module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClOmMain
public import CFSG.LocalAnalysis.ComponentClassification.EvenOrthSelector

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation
open CFSG.SeitzReduction.RankOne

theorem oddU42Free_POmegaOdd : OddU42Free .POmegaOdd := by
  apply oddU42Free_of_concrete
  intro S _ _ n f hadm hm
  have hf : 1 ≤ f := hadm.2.1
  have hn : 3 ≤ n := hadm.2.2.1
  have hstated : StatedClassicalModel S .POmegaOdd n 3 f :=
    EvenOrthSelector.statedModel_of_lieModel (by decide) hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hstated
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaOdd (Or.inl rfl)
    hstated K hK e
  let ψ := coordinateOddWitnessEquiv K e
  refine ⟨matrixProjectiveDerived (coordinateQuadOdd n K), inferInstance,
    Finite.of_equiv S ψ.toEquiv, ψ, ?_⟩
  intro σ J hσ hJ
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (u42_ringChar_ne_two hf hK)
  obtain ⟨-, hnd, -⟩ := coordinate_model_witness_odd hstated K hK e
  let P := fun i : Fin n =>
    ClTwoPart.hypPairMap (coordinateOddIsometry n K) (ClassicalGroups.Orthogonal.oddPair K i)
  have hP : ∀ {i j : Fin n}, i ≠ j → (P i).Orth (P j) := fun hij =>
    ClTwoPart.hypPairMap_orth _ (ClassicalGroups.Orthogonal.oddPair_orth hij)
  have hidx := ClTwoPart.index_orthogonalDerived_eq_four h2 hnd
    (hP (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp [Fin.ext_iff]))
    (hP (i := ⟨0, by omega⟩) (j := ⟨2, by omega⟩) (by simp [Fin.ext_iff]))
    (hP (i := ⟨1, by omega⟩) (j := ⟨2, by omega⟩) (by simp [Fin.ext_iff]))
  exact u42_omega_false hf hK (by omega) hnd hidx hrep hσ hJ

theorem oddU42Free_POmegaPlus : OddU42Free .POmegaPlus := by
  apply oddU42Free_of_concrete
  intro S _ _ n f hadm hm
  have hf : 1 ≤ f := hadm.2.1
  have hn : 4 ≤ n := hadm.2.2
  have hstated : StatedClassicalModel S .POmegaPlus n 3 f :=
    EvenOrthSelector.statedModel_of_lieModel (by decide) hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hstated
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaPlus
    (Or.inr (Or.inl rfl)) hstated K hK e
  let ψ := coordinatePlusWitnessEquiv K e
  refine ⟨matrixProjectiveDerived (coordinateQuadPlus n K), inferInstance,
    Finite.of_equiv S ψ.toEquiv, ψ, ?_⟩
  intro σ J hσ hJ
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (u42_ringChar_ne_two hf hK)
  obtain ⟨-, hnd, -⟩ := coordinate_model_witness_plus hstated K hK e
  let P := fun i : Fin n =>
    ClTwoPart.hypPairMap (coordinatePlusIsometry n K) (ClassicalGroups.Orthogonal.plusPair K i)
  have hP : ∀ {i j : Fin n}, i ≠ j → (P i).Orth (P j) := fun hij =>
    ClTwoPart.hypPairMap_orth _ (ClassicalGroups.Orthogonal.plusPair_orth hij)
  have hidx := ClTwoPart.index_orthogonalDerived_eq_four h2 hnd
    (hP (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp [Fin.ext_iff]))
    (hP (i := ⟨0, by omega⟩) (j := ⟨2, by omega⟩) (by simp [Fin.ext_iff]))
    (hP (i := ⟨1, by omega⟩) (j := ⟨2, by omega⟩) (by simp [Fin.ext_iff]))
  exact u42_omega_false hf hK (by omega) hnd hidx hrep hσ hJ

theorem oddU42Free_POmegaMinus : OddU42Free .POmegaMinus := by
  apply oddU42Free_of_concrete
  intro S _ _ n f hadm hm
  have hf : 1 ≤ f := hadm.2.1
  have hn4 : 4 ≤ n := hadm.2.2
  have hn : 1 ≤ n := by omega
  have hstated : StatedClassicalModel S .POmegaMinus n 3 f :=
    EvenOrthSelector.statedModel_of_lieModel (by decide) hm
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := id hstated
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaMinus
    (Or.inr (Or.inr rfl)) hstated hn K hK b c hirr e
  let ψ := coordinateMinusWitnessEquiv K hn b c e
  refine ⟨matrixProjectiveDerived (coordinateQuadMinus n K hn b c), inferInstance,
    Finite.of_equiv S ψ.toEquiv, ψ, ?_⟩
  intro σ J hσ hJ
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (u42_ringChar_ne_two hf hK)
  obtain ⟨-, hnd, -⟩ := coordinate_model_witness_minus hstated K hK b c hirr e
  let P := fun i : Fin (n - 1) =>
    ClTwoPart.hypPairMap (coordinateMinusIsometry n K hn b c)
      (ClassicalGroups.Orthogonal.minusPair (n := n) K b c i)
  have hP : ∀ {i j : Fin (n - 1)}, i ≠ j → (P i).Orth (P j) := fun hij =>
    ClTwoPart.hypPairMap_orth _ (ClassicalGroups.Orthogonal.minusPair_orth hij)
  have hidx := ClTwoPart.index_orthogonalDerived_eq_four h2 hnd
    (hP (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp [Fin.ext_iff]))
    (hP (i := ⟨0, by omega⟩) (j := ⟨2, by omega⟩) (by simp [Fin.ext_iff]))
    (hP (i := ⟨1, by omega⟩) (j := ⟨2, by omega⟩) (by simp [Fin.ext_iff]))
  exact u42_omega_false hf hK (by omega) hnd hidx hrep hσ hJ

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
