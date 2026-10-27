module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscSteps185
public import CFSG.ClassicalInvolution.AschTight.Sec6GenAPI
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

namespace TwinThmE

section Pf2Base

theorem exists_orderOf_eq_four_of_mem_RSet_gen {G : Type} [Group G] [Finite G]
    {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {R : Subgroup G} (hR : R ∈ RSet Ω) :
    ∃ u ∈ R, orderOf u = 4 := by
  have hquat := Sec6Gen.isQuatSub_of_mem_RSet hΩ hR
  obtain ⟨C, hCR, hC, hcard, -⟩ := hquat.exists_cyclic_max
  obtain ⟨J, -, -, hR2, -⟩ := mem_RSet_iff.mp hR
  have h8 := hquat.eight_le
  obtain ⟨x, hxC, hx⟩ := exists_orderOf_eq_four_of_isPGroup_of_isCyclic (hR2.to_le hCR) hC
    (by omega)
  exact ⟨x, hCR hxC, hx⟩

end Pf2Base

end TwinThmE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
