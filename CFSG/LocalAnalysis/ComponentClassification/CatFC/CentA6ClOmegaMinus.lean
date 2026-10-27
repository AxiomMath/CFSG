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

theorem oddA6Shape_POmegaMinus
    (hO : LieOrderFormulasInput) (hgls : GLS3OddFamilyInput .POmegaMinus) :
    OddA6Shape .POmegaMinus := by
  refine oddA6Shape_of_concrete fun S _ _ n p f hp hp2 hadm hm => ?_
  have hn : 1 ≤ n := by have := hadm.2.2; omega
  have hC : StatedClassicalModel S .POmegaMinus n p f :=
    EvenOrthSelector.statedModel_of_lieModel (by decide) hm
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hC
  let Q := coordinateQuadMinus n K hn b c
  let iso := coordinateMinusWitnessEquiv K hn b c e
  have hfin : Finite (matrixProjectiveDerived Q) := Finite.of_equiv S iso.toEquiv
  refine ⟨matrixProjectiveDerived Q, inferInstance, hfin, iso, fun σ D hσ hD => ?_⟩
  have hm' := LieType.CurtisTits.lieModel_of_mulEquiv iso hm
  have hp3 : p = 3 := hD.char_three hO hgls hp hp2 hadm hm' hσ
  subst hp3
  have hstated : StatedClassicalModel S .POmegaMinus n 3 f := ⟨hadm, K, inferInstance, inferInstance,
    hK, b, c, hirr, ⟨e⟩⟩
  obtain ⟨-, hnd, -⟩ := coordinate_model_witness_minus hstated K hK b c hirr e
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaMinus
    (Or.inr (Or.inr rfl)) hstated hn K hK b c hirr e
  obtain ⟨hf1, hres⟩ := omega_X_core hadm.2.1 hK (Or.inr ⟨rfl, hadm.2.2⟩) Q hnd hrep hO σ hσ hD
  refine ⟨rfl, ?_, fun h => absurd h (by decide)⟩
  rcases hres with h7 | ⟨h8, -⟩
  · omega
  · have hn4 : n = 4 := by omega
    unfold A6Shape
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hn4, hf1⟩)))))))

end CFSG.ComponentClassification.CatFC
