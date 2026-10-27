module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.RootTuples
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Frames
public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint

@[expose] def theta : Fin Tag.E8.rank → ℤ := ![2, 3, 4, 6, 5, 4, 3, 2]

theorem theta_eq : theta = highRoot .E8 := rfl

@[expose] def S1set : Set (Fin Tag.E8.rank → ℤ) := {r | r ∈ e8ListB}

@[expose] def S2set : Set (Fin Tag.E8.rank → ℤ) := {r | r ∈ e8ListA}

@[expose] def mRoots : Finset (Fin Tag.E8.rank → ℤ) :=
  (rootFinset .E8).filter fun β => β 7 = 1 ∧ β 4 % 5 ≠ 0

@[expose] def sRoots1 : Finset (Fin Tag.E8.rank → ℤ) :=
  (rootFinset .E8).filter fun β => β 7 = 1 ∧ β 4 % 5 = 0

@[expose] def deg1Roots : Finset (Fin Tag.E8.rank → ℤ) :=
  (rootFinset .E8).filter fun β => β 7 = 1

@[expose] def pureNegDirs : Finset (Fin Tag.E8.rank → ℤ) :=
  (rootFinset .E8).filter fun β => β 7 = -1 ∧ β 4 % 5 = 0

theorem theta_mem : theta ∈ rootFinset .E8 := by
  rw [rootFinset_E8_eq]
  decide +kernel

theorem card_mRoots : mRoots.card = 50 := by
  simp only [mRoots, rootFinset_E8_eq]
  decide +kernel

theorem card_sRoots1 : sRoots1.card = 6 := by
  simp only [sRoots1, rootFinset_E8_eq]
  decide +kernel

theorem card_deg1Roots : deg1Roots.card = 56 := by
  simp only [deg1Roots, rootFinset_E8_eq]
  decide +kernel

theorem card_pureNegDirs : pureNegDirs.card = 6 := by
  simp only [pureNegDirs, rootFinset_E8_eq]
  decide +kernel

theorem deg_bounds : ∀ β ∈ rootFinset .E8, -2 ≤ β 7 ∧ β 7 ≤ 2 := by
  rw [rootFinset_E8_eq]
  decide +kernel

theorem deg_eq_two : ∀ β ∈ rootFinset .E8, β 7 = 2 → β = theta := by
  rw [rootFinset_E8_eq]
  decide +kernel

theorem deg_eq_neg_two : ∀ β ∈ rootFinset .E8, β 7 = -2 → β = -theta := by
  rw [rootFinset_E8_eq]
  decide +kernel

theorem deg_eq_pairing : ∀ β ∈ rootFinset .E8,
    2 * iform β theta = iform theta theta * β 7 := by
  rw [rootFinset_E8_eq]
  decide +kernel

theorem commCandidates_theta_data : ∀ β ∈ rootFinset .E8, (β 7 = 0 ∨ β 7 = 1) →
    ∀ p ∈ commCandidates, p.1 • theta + p.2 • β ∉ rootFinset .E8 := by
  rw [rootFinset_E8_eq]
  decide +kernel

theorem theta_ne_of_deg : ∀ β ∈ rootFinset .E8, (β 7 = 0 ∨ β 7 = 1) → theta ≠ β ∧ theta ≠ -β := by
  rw [rootFinset_E8_eq]
  decide +kernel

theorem deg_one_roots : ∀ β ∈ rootFinset .E8, β 7 = 1 → β ∈ mRoots ∨ β ∈ sRoots1 := by
  simp only [mRoots, sRoots1, rootFinset_E8_eq]
  decide +kernel

theorem S_data : ∀ β ∈ rootFinset .E8, β 4 % 5 = 0 → β ∈ e8ListA ∨ β ∈ e8ListB := by
  rw [rootFinset_E8_eq]
  decide +kernel

section Mem


theorem mem_mRoots {β : Fin Tag.E8.rank → ℤ} :
    β ∈ mRoots ↔ IsRoot Tag.E8 β ∧ β 7 = 1 ∧ β 4 % 5 ≠ 0 := by
  rw [mRoots, Finset.mem_filter, mem_rootFinset]

theorem mem_sRoots1 {β : Fin Tag.E8.rank → ℤ} :
    β ∈ sRoots1 ↔ IsRoot Tag.E8 β ∧ β 7 = 1 ∧ β 4 % 5 = 0 := by
  rw [sRoots1, Finset.mem_filter, mem_rootFinset]

theorem mem_deg1Roots {β : Fin Tag.E8.rank → ℤ} : β ∈ deg1Roots ↔ IsRoot Tag.E8 β ∧ β 7 = 1 := by
  rw [deg1Roots, Finset.mem_filter, mem_rootFinset]

theorem mem_pureNegDirs {β : Fin Tag.E8.rank → ℤ} :
    β ∈ pureNegDirs ↔ IsRoot Tag.E8 β ∧ β 7 = -1 ∧ β 4 % 5 = 0 := by
  rw [pureNegDirs, Finset.mem_filter, mem_rootFinset]

end Mem

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
