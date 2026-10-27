module

public import CFSG.ClassicalInvolution.Asc77.AscIH8Model
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen69
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Asc77

namespace Asc77

section Hosts


abbrev OmegaLie {G : Type} [Group G] (Ω : Set (Subgroup G)) :=
  CFSG.ClassicalInvolution.Asc77.OmegaLie 3 1 Ω

abbrev Ih8Model {G : Type} [Group G] (Ω : Set (Subgroup G))
    (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (k e : ℕ) :=
  CFSG.ClassicalInvolution.Asc77.Ih8Model 3 1 Ω t k e

end Hosts

section Six

open CFSG.ClassicalInvolution.Disconnected.AschTight

alias exists_invariant_mem_etaSet := Sec6Gen.exists_invariant_mem_etaSet

end Six

end Asc77

end CFSG.ClassicalInvolution.Q3.Q3T8
