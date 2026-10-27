module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaX
public import CFSG.LocalAnalysis.ComponentClassification.EvenOrthSelector

public noncomputable section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeafProof CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation

theorem oddA6Shape_POmegaOdd
    (hO : LieOrderFormulasInput) (hgls : GLS3OddFamilyInput .POmegaOdd) :
    OddA6Shape .POmegaOdd := by
  refine oddA6Shape_of_concrete fun S _ _ n p f hp hp2 hadm hm => ?_
  have hC : StatedClassicalModel S .POmegaOdd n p f :=
    EvenOrthSelector.statedModel_of_lieModel (by decide) hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hC
  let Q := coordinateQuadOdd n K
  let iso := coordinateOddWitnessEquiv K e
  have hfin : Finite (matrixProjectiveDerived Q) := Finite.of_equiv S iso.toEquiv
  refine ⟨matrixProjectiveDerived Q, inferInstance, hfin, iso, fun σ D hσ hD => ?_⟩
  have hm' := LieType.CurtisTits.lieModel_of_mulEquiv iso hm
  have hp3 : p = 3 := hD.char_three hO hgls hp hp2 hadm hm' hσ
  subst hp3
  have hstated : StatedClassicalModel S .POmegaOdd n 3 f := ⟨hadm, K, inferInstance, inferInstance,
    hK, ⟨e⟩⟩
  obtain ⟨-, hnd, -⟩ := coordinate_model_witness_odd hstated K hK e
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaOdd (Or.inl rfl)
    hstated K hK e
  obtain ⟨hf1, hres⟩ := omega_X_core hadm.2.1 hK (Or.inl ⟨rfl, hadm.2.2.1⟩) Q hnd hrep hO σ hσ hD
  refine ⟨rfl, ?_, fun h => absurd h (by decide)⟩
  rcases hres with h7 | ⟨h8, -⟩
  · have hn3 : n = 3 := by omega
    unfold A6Shape
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hn3, hf1⟩)))))))
  · omega

end CFSG.ComponentClassification.CatFC
