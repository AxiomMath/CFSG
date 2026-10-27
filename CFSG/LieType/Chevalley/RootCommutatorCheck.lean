module

public import CFSG.LieType.Chevalley.RootCommutatorData

public section

namespace CFSG.LieType.Chevalley.RootOps

open CFSG.Blueprint.Chevalley

theorem repShapeCheck_G2 : (repsOf .G2).all (repShapeCheck .G2 (commConstBound .G2)) = true := by
  decide +kernel

theorem repShapeCheck_F4 : (repsOf .F4).all (repShapeCheck .F4 (commConstBound .F4)) = true := by
  decide +kernel

theorem repShapeCheck_D4 : (repsOf .D4).all (repShapeCheck .D4 (commConstBound .D4)) = true := by
  decide +kernel

theorem repShapeCheck_E6 : (repsOf .E6).all (repShapeCheck .E6 (commConstBound .E6)) = true := by
  decide +kernel

theorem repShapeCheck_E7 : (repsOf .E7).all (repShapeCheck .E7 (commConstBound .E7)) = true := by
  decide +kernel

theorem repShapeCheck_E8 : (repsOf .E8).all (repShapeCheck .E8 (commConstBound .E8)) = true := by
  decide +kernel

theorem longestCheck_G2
    : longestCheck .G2 = true := by decide +kernel

theorem longestCheck_F4
    : longestCheck .F4 = true := by decide +kernel

theorem longestCheck_D4
    : longestCheck .D4 = true := by decide +kernel

theorem longestCheck_E6
    : longestCheck .E6 = true := by decide +kernel

theorem longestCheck_E7
    : longestCheck .E7 = true := by decide +kernel

theorem longestCheck_E8
    : longestCheck .E8 = true := by decide +kernel

theorem simplyLacedCheck_D4 : simplyLacedCheck .D4 = true := by decide +kernel

theorem simplyLacedCheck_E6 : simplyLacedCheck .E6 = true := by decide +kernel

theorem simplyLacedCheck_E7 : simplyLacedCheck .E7 = true := by decide +kernel

theorem simplyLacedCheck_E8 : simplyLacedCheck .E8 = true := by decide +kernel

theorem repShapeCheck_repsOf :
    ∀ τ : Tag, (repsOf τ).all (repShapeCheck τ (commConstBound τ)) = true
  | .G2 => repShapeCheck_G2
  | .F4 => repShapeCheck_F4
  | .D4 => repShapeCheck_D4
  | .E6 => repShapeCheck_E6
  | .E7 => repShapeCheck_E7
  | .E8 => repShapeCheck_E8

theorem simplyLacedCheck_eq {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    simplyLacedCheck τ = true := by
  rcases hτ with rfl | rfl | rfl | rfl
  · exact simplyLacedCheck_D4
  · exact simplyLacedCheck_E6
  · exact simplyLacedCheck_E7
  · exact simplyLacedCheck_E8

theorem longestCheck_eq
    : ∀ τ : Tag, longestCheck τ = true
  | .G2 => longestCheck_G2
  | .F4 => longestCheck_F4
  | .D4 => longestCheck_D4
  | .E6 => longestCheck_E6
  | .E7 => longestCheck_E7
  | .E8 => longestCheck_E8

end CFSG.LieType.Chevalley.RootOps
