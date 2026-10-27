module

public import CFSG.LieType.Chevalley.RootCommutatorPairs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Steinberg.Adjoint.Pairs
public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint

@[expose] def theta : Fin Tag.F4.rank → ℤ := ![2, 3, 4, 2]

theorem theta_eq : theta = highRoot .F4 := rfl

@[expose] def alpha1 : Fin Tag.F4.rank → ℤ := ![1, 0, 0, 0]

@[expose] def root1342 : Fin Tag.F4.rank → ℤ := ![1, 3, 4, 2]

@[expose] def mRoots : List (Fin Tag.F4.rank → ℤ) :=
  [![1, 1, 0, 0], ![1, 1, 1, 0], ![1, 1, 1, 1], ![1, 1, 2, 0], ![1, 1, 2, 1], ![1, 1, 2, 2],
    ![1, 2, 2, 0], ![1, 2, 2, 1], ![1, 2, 2, 2], ![1, 2, 3, 1], ![1, 2, 3, 2], ![1, 2, 4, 2]]

@[expose] def sRoots1 : List (Fin Tag.F4.rank → ℤ) := [![1, 0, 0, 0], ![1, 3, 4, 2]]

theorem theta_mem : theta ∈ rootFinset .F4 := by decide +kernel

theorem deg_bounds : ∀ β ∈ rootFinset .F4, -2 ≤ β 0 ∧ β 0 ≤ 2 := by decide +kernel

theorem deg_eq_two : ∀ β ∈ rootFinset .F4, β 0 = 2 → β = theta := by decide +kernel

theorem deg_eq_neg_two : ∀ β ∈ rootFinset .F4, β 0 = -2 → β = -theta := by decide +kernel

theorem deg_eq_pairing : ∀ β ∈ rootFinset .F4,
    2 * iform β theta = iform theta theta * β 0 := by decide +kernel

theorem commCandidates_theta_data : ∀ β ∈ rootFinset .F4, (β 0 = 0 ∨ β 0 = 1) →
    ∀ p ∈ commCandidates, p.1 • theta + p.2 • β ∉ rootFinset .F4 := by decide +kernel

theorem theta_ne_of_deg : ∀ β ∈ rootFinset .F4, (β 0 = 0 ∨ β 0 = 1) → theta ≠ β ∧ theta ≠ -β := by
  decide +kernel

theorem deg_one_roots : ∀ β ∈ rootFinset .F4, β 0 = 1 →
    (β ∈ mRoots ∧ β 1 % 3 ≠ 0) ∨ (β ∈ sRoots1 ∧ β 1 % 3 = 0) := by decide +kernel

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4
