module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.Frame
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.RootData

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint

@[expose] def leviWord : List (Fin Tag.F4.rank) := [1, 2, 1, 3, 2, 1, 0]

theorem leviWord_theta : leviWord.foldr (reflect .F4) theta = alpha1 := by decide +kernel

theorem leviWord_min : ∀ β ∈ rootFinset .F4, β 0 = 0 → 0 < height β →
    0 < height (leviWord.foldr (reflect .F4) β) := by decide +kernel

theorem perp_inter_F4 : ∀ β ∈ rootFinset .F4, (β 0 = 0 ∧ 0 < height β) →
    ((leviWord.reverse.foldr (reflect .F4) β) 0 = 0 ∧
      0 < height (leviWord.reverse.foldr (reflect .F4) β)) →
    β ∈ f4ShortList ∧ 0 < height β := by decide +kernel

theorem S2_eq_supp : ∀ β ∈ rootFinset .F4, (β 0 = 0 ∧ β 1 = 0) → β ∈ f4ShortList := by
  decide +kernel

theorem theta_mem_S1set : theta ∈ S1set := by
  show theta ∈ f4LongList
  decide +kernel
theorem neg_theta_mem_S1set : -theta ∈ S1set := by
  show -theta ∈ f4LongList
  decide +kernel
theorem alpha1_mem_S1set : alpha1 ∈ S1set := by
  show alpha1 ∈ f4LongList
  decide +kernel
theorem neg_alpha1_mem_S1set : -alpha1 ∈ S1set := by
  show -alpha1 ∈ f4LongList
  decide +kernel

set_option linter.unusedSectionVars false


@[expose] def w₁ : WeylGroup Tag.F4 := (coxeterSystem Tag.F4).wordProd leviWord

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4
