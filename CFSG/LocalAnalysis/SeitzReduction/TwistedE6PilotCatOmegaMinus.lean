module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCatOmegaMinusSporadic
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatAssembly
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)
open CFSG.SeitzReduction.F4Pilot (centerQuotientAut FixedCentralizerTwoFree)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)
open CFSG.SeitzReduction.OmegaPilot (CatOmegaSporadicAt OmegaCatalogueClausesAt OmegaOvergroup
  OmegaNotOddLieInputAt)

theorem four_ne_four_one {f : ℕ} (hf : 2 ≤ f) : ((4 : ℕ), f) ≠ (4, 1) := fun h => by
  have := congrArg Prod.snd h
  simp only at this
  omega

theorem catOmegaSporadicAt_four_of_monster (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) : CatOmegaSporadicAt 4 := by
  intro S _ _ hS hna hsp σ hσ t f D ht hD hDm _
  refine ⟨rfl, ?_⟩
  have hf : 1 ≤ f := OmegaPilot.one_le_of_lieModel_POmega ht hDm
  by_contra hf1
  exact false_of_sporadic_POmega_four_of_two_le hMinn hMcomp hS hna hsp hσ ht (by omega) hD hDm

section Clauses

theorem omegaCatalogueClausesAt_four_of_leafInputs (hGLS : GLS3OddLieAutComponentsInput)
    (hX : OmegaNotOddLieInputAt 4) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) : OmegaCatalogueClausesAt 4 :=
  OmegaPilot.omegaCatalogueClausesAt_of_inputs hGLS hX
    (catOmegaSporadicAt_four_of_monster hMinn hMcomp)

end Clauses

end CFSG.SeitzReduction.TwistedE6Pilot
