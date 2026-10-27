module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.RootData

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint

theorem lemma2_core : ∀ γ ∈ mRoots, ∀ β ∈ sRoots1, γ + β ∉ rootFinset .F4 := by decide +kernel

theorem case3_data : ∀ β ∈ rootFinset .F4, β 0 = -1 → iform β β = iform theta theta →
    (theta + β ∈ rootFinset .F4 ∧ (theta + β) 0 = 1) ∧ β - theta ∉ rootFinset .F4 ∧
    theta ≠ β ∧ theta ≠ -β ∧ theta + β ≠ theta ∧ theta + β ≠ -theta ∧
    (∀ p ∈ commCandidates, p.1 • theta + p.2 • β ∈ rootFinset .F4 ↔ p = (1, 1)) ∧
    (∀ p ∈ commCandidates, p.1 • (theta + β) + p.2 • theta ∉ rootFinset .F4) := by
  decide +kernel

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4
