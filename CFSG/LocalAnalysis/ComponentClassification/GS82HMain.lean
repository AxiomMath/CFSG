module

public import CFSG.LocalAnalysis.ComponentClassification.GS82HConfigCtx
public import CFSG.GH74.GLS.TwoThin.Basic
public import CFSG.GH74.Generic.BProg.B1.PilotS1ThreeFacts

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup
open scoped MatrixGroups

theorem not_gs82HConfig_three {X : Type} [Group X] [Finite X] {t : X} {K R T : Subgroup X}
    {w : X} : ¬ GS82HConfig 3 t K R T w := by
  rintro ⟨-, -, -, -, -, -, hTKR, hTc, ⟨F, hF, hFt, hFq, ⟨eT⟩⟩, -, -, -⟩
  have hTq : IsQuasisimple (↥T ⧸ pPrimeCore 2 ↥T) := by
    obtain ⟨e⟩ := HConfig.nonempty_quot_equiv_of_mulEquiv (subgroupOfEquivOfLe hTKR)
    exact LocalCores.isQuasisimple_of_mulEquiv e
      (GH74.GLS.TwoThin.isQuasisimple_hat_of_isPComponent hTc)
  have hS : Group.IsSolvable SL(2, F) :=
    GH74.Generic.BProg.B1.PilotS1.isSolvable_sl2_three (by rw [Nat.card_eq_fintype_card, hFq])
  exact not_isSolvable_of_isQuasisimple hTq
    (solvable_of_surjective (f := eT.symm.toMonoidHom) eT.symm.surjective)

end CFSG.ComponentClassification.GSThmB
