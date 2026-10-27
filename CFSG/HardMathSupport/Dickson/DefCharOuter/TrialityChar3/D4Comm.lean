module

public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Lang.E27Lie.CocycleCount
public import CFSG.HardMathSupport.Lang.Triality.SylowInnerExt
public import CFSG.HardMathSupport.Solomon.Coordinator.B3RedAlg
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.Triality CFSG.HardMathSupport.Lang.E27Lie
open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3


abbrev rootA0 : Fin TwistTag.D4.tag.rank → ℤ := ![1, 0, 0, 0]
abbrev rootA1 : Fin TwistTag.D4.tag.rank → ℤ := ![0, 1, 0, 0]
abbrev rootA3 : Fin TwistTag.D4.tag.rank → ℤ := ![0, 0, 0, 1]

section D4Comm

variable {K : Type} [Field K]

theorem exists_commutator_pinnedX_of_sum {α β γ : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : IsRoot TwistTag.D4.tag α) (hβ : IsRoot TwistTag.D4.tag β) (hne : α ≠ β) (hne' : α ≠ -β)
    (hsum : α + β = γ) (hγ : IsRoot TwistTag.D4.tag γ) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ c d : K,
      ⁅pinnedX TwistTag.D4.tag K α c, pinnedX TwistTag.D4.tag K β d⁆ = pinnedX TwistTag.D4.tag K γ (ε * c * d) := by
  subst hsum
  obtain ⟨hε, hf⟩ := (simply_laced_root_commutator_unit TwistTag.D4.tag (Or.inl rfl) hα hβ hne
    hne').1 hγ
  refine ⟨(commConst TwistTag.D4.tag α β (1, 1) : K), ?_, fun c d => hf K c d⟩
  rcases hε with h | h <;> simp [h]

theorem commute_pinnedX_of_not_isRoot_add {α β : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : IsRoot TwistTag.D4.tag α) (hβ : IsRoot TwistTag.D4.tag β) (hne : α ≠ β) (hne' : α ≠ -β)
    (hn : ¬ IsRoot TwistTag.D4.tag (α + β)) (c d : K) :
    Commute (pinnedX TwistTag.D4.tag K α c) (pinnedX TwistTag.D4.tag K β d) :=
  (simply_laced_root_commutator_unit TwistTag.D4.tag (Or.inl rfl) hα hβ hne hne').2 hn K _
    (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨d, rfl⟩)

end D4Comm

end CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
