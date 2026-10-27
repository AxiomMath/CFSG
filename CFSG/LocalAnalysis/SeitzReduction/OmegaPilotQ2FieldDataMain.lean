module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2FieldDataChart
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2FieldMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.LinearPilot (consecutiveBlock)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus
  coordinateQuadMinus)

section Data

variable {G : Type} [Group G]

variable [Finite G] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem q2NbrCore_le_anisoNeighbourJoin {L X : Subgroup G} {r : ℕ}
    {τ : (Fin (r + 1) → Fˣ) →* G} {k : Fin (r + 1)} {l : L}
    (hl : (rootParam k).map τ = X.map (MulAut.conj (l : G)).toMonoidHom) :
    q2NbrCore τ k ≤ anisoNeighbourJoin L X := by
  change centralizerPerfectCore ((rootParam k).map τ) ≤ _
  rw [hl]
  exact centralizerPerfectCore_le_anisoNeighbourJoin L X l

end Data

end CFSG.SeitzReduction.OmegaPilot
