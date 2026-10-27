module

public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecOrthMain
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecAssembly

public noncomputable section

namespace CFSG.ComponentClassification.Sp4Rec

open CFSG Subgroup Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare

attribute [local instance] finite_linearEquiv'

namespace Config

variable {H : Type} [Group H] [Finite H] (c : Sp4Rec.Config H)

include c in
theorem false_of_orthogonal {t : StatedLieTag} {n p f : ℕ} (hp2 : p ≠ 2)
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (hG : StatedClassicalModel ↥(generalizedFitting H) t n p f) : False := by
  rcases ht with rfl | rfl | rfl
  · obtain ⟨⟨hp, hf, hn, -⟩, K, _, _, hK, ⟨φ⟩⟩ := id hG
    obtain ⟨-, hnd, -⟩ := coordinate_model_witness_odd hG K hK φ
    exact pairConfig_orthogonalProj_false hp hp2 hf hK (by rw [Module.finrank_fin_fun]; omega)
      hnd (c.pairConfig ((coordinateOddWitnessEquiv K φ).trans
        (LocalAnalysis.ComponentInitial.OddOrthogonal.projEquiv _ (by omega))))
  · obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, ⟨φ⟩⟩ := id hG
    obtain ⟨-, hnd, -⟩ := coordinate_model_witness_plus hG K hK φ
    exact pairConfig_orthogonalProj_false hp hp2 hf hK (by rw [Module.finrank_fin_fun]; omega)
      hnd (c.pairConfig ((coordinatePlusWitnessEquiv K φ).trans
        (LocalAnalysis.ComponentInitial.OddOrthogonal.projEquiv _ (by omega))))
  · obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, b, c', hirr, ⟨φ⟩⟩ := id hG
    obtain ⟨-, hnd, -⟩ := coordinate_model_witness_minus hG K hK b c' hirr φ
    exact pairConfig_orthogonalProj_false hp hp2 hf hK (by rw [Module.finrank_fin_fun]; omega)
      hnd (c.pairConfig ((coordinateMinusWitnessEquiv K (by omega) b c' φ).trans
        (LocalAnalysis.ComponentInitial.OddOrthogonal.projEquiv _ (by omega))))

end Config

theorem orthogonalExclusion : OrthogonalExclusion :=
  fun _ _ _ c _ _ _ _ _ hp2 ht hG => c.false_of_orthogonal hp2 ht hG

theorem cfSp4RecognitionCI_of_L4U4 (hL : LinearFourExclusion) (hU : UnitaryFourExclusion) :
    GSThmB.CFSp4RecognitionCI :=
  cfSp4RecognitionCI_of_four hL hU orthogonalExclusion

end CFSG.ComponentClassification.Sp4Rec
