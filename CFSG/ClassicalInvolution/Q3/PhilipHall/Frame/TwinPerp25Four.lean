module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.HypOmegaDefs
public import CFSG.ClassicalInvolution.AschTight.S19COrd
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.Assembly.LowTwoRank

section Layer

variable {G : Type} [Group G]

@[expose] def layerX (Ω : Set (Subgroup G)) (c : G) : Subgroup G :=
  Subgroup.closure {x | ∃ R₀ ∈ RSet Ω, R₀ ≤ Subgroup.centralizer ({c} : Set G) ∧ x ∈ R₀}

abbrev layerBar (Ω : Set (Subgroup G)) (c : G) : Type :=
  ↥(layerX Ω c) ⧸ classicalInvolutionOddCore ↥(layerX Ω c)

end Layer

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R
