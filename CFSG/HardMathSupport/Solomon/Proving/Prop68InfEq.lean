module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7ToolsB
public import CFSG.HardMathSupport.Solomon.Coordinator.Defs
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Proving

variable {G : Type} [Group G] [Finite G]

theorem center_eq_bot_of_isLThreeFour' {X : Type} [Group X] (h : IsLThreeFour X) :
    Subgroup.center X = ⊥ := by
  obtain ⟨_, a, b, hab⟩ := isSimpleGroup_of_isLThreeFour h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with hc | hc
  · exact hc
  · have hb : b ∈ Subgroup.center X := by
      rw [hc]
      exact Subgroup.mem_top b
    exact absurd (Subgroup.mem_center_iff.mp hb a) hab

end CFSG.HardMathSupport.Solomon.Proving

end
