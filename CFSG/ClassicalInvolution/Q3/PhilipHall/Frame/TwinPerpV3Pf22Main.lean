module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf21Vertex
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf15Three
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf8Vertex

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open scoped commutatorElement

section Six

section Fam

variable {n : ℕ}

theorem v3Hyp51U_of_model (hSp : ModelFactSp62) (hD4 : ModelFactD42) (hM12 : ModelFactM12)
    (h4 : Thm4RTwinBelow 3 n) (hU3 : V3Hyp51U3E8 n) : V3Hyp51U n := by
  classical
  refine v3Hyp51U_of_vertex ?_
  intro Y _ _ R S t hP h3 hE K K' K₃ u₁ u₂ u₃ d
  by_cases h4tw : ∃ K₄ ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K,
      K₄ ≠ K ∧ K₄ ≠ K' ∧ K₄ ≠ K₃
  · obtain ⟨K₄, hK₄, h41, h42, h43⟩ := h4tw
    exact v3Hyp51U1_of_model hSp hD4 hM12 h4 hP d hK₄ h41 h42 h43
  · push Not at h4tw
    exact v3Hyp51U3_of_conn hU3 Y R S t hP h3 hE K K' K₃ u₁ u₂ u₃ d (fun M hM => by
      by_cases h1 : M = K
      · exact Or.inl h1
      by_cases h2 : M = K'
      · exact Or.inr (Or.inl h2)
      exact Or.inr (Or.inr (h4tw M hM h1 h2)))

end Fam

end Six

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
