module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.RootData

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint

theorem lemma2_core : ∀ γ ∈ mRoots, ∀ β ∈ sRoots1, γ + β ∉ rootFinset .E8 := by
  simp only [mRoots, sRoots1, rootFinset_E8_eq]
  decide +kernel

theorem case3_data : ∀ β ∈ rootFinset .E8, β 7 = -1 →
    (theta + β ∈ rootFinset .E8 ∧ (theta + β) 7 = 1) ∧ theta ≠ β ∧ theta ≠ -β ∧
    theta + β ≠ theta ∧ theta + β ≠ -theta ∧ (theta + β) + theta ∉ rootFinset .E8 := by
  rw [rootFinset_E8_eq]
  decide +kernel

theorem pureNeg_data : ∀ ν ∈ pureNegDirs, -ν ∈ e8ListB ∧ -ν ∈ sRoots1 := by
  simp only [pureNegDirs, sRoots1, rootFinset_E8_eq]
  decide +kernel

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
