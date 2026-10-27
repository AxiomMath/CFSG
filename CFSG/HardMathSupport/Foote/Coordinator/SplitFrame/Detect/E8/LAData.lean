module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.RootData

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint

@[expose] def lxPos : Finset (Fin Tag.E8.rank → ℤ) :=
  (rootFinset .E8).filter fun γ => γ 7 = 0 ∧ γ 4 % 5 = 0 ∧ 0 < height γ

@[expose] def lxRoots : Finset (Fin Tag.E8.rank → ℤ) :=
  (rootFinset .E8).filter fun γ => γ 7 = 0 ∧ γ 4 % 5 = 0

@[expose] def topsE8 : Finset (Fin Tag.E8.rank → ℤ) :=
  {![1, 1, 2, 2, 1, 1, 1, 1], ![1, 2, 2, 3, 2, 2, 2, 1], ![2, 2, 3, 4, 3, 3, 2, 1],
    ![2, 3, 4, 6, 4, 3, 2, 1]}

@[expose] def Adm (a : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ) → ℤ) : Prop :=
  ∀ γ ∈ rootFinset .E8, γ 7 = 0 → ∀ μ ∈ deg1Roots,
    (γ + μ ∈ rootFinset .E8 → |a γ μ| = 1) ∧ (γ + μ ∉ rootFinset .E8 → a γ μ = 0)

@[expose] def actFun {K : Type} [Field K]
    (a : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ) → ℤ) (γ : Fin Tag.E8.rank → ℤ)
    (t : K) (c : (Fin Tag.E8.rank → ℤ) → K) : (Fin Tag.E8.rank → ℤ) → K :=
  fun ν => c ν + t * (a γ (ν - γ) : K) * c (ν - γ)

theorem lxPos_data : ∀ γ ∈ lxPos, γ ∈ rootFinset .E8 ∧ γ 7 = 0 ∧ γ 4 % 5 = 0 ∧ 0 < height γ :=
  fun _ hγ => Finset.mem_filter.1 hγ

theorem card_lxPos : lxPos.card = 13 := by
  simp only [lxPos, rootFinset_E8_eq]
  decide +kernel

theorem card_lxRoots : lxRoots.card = 26 := by
  simp only [lxRoots, rootFinset_E8_eq]
  decide +kernel

theorem lxRoots_data : ∀ γ ∈ lxRoots, γ ∈ rootFinset .E8 ∧ γ 7 = 0 ∧ γ 4 % 5 = 0 :=
  fun _ hγ => Finset.mem_filter.1 hγ

theorem topsE8_data : ∀ μ ∈ topsE8, μ ∈ mRoots := by
  simp only [topsE8, mRoots, rootFinset_E8_eq]
  decide +kernel

theorem non_top : ∀ μ ∈ mRoots, μ ∉ topsE8 → ∃ γ ∈ lxPos, γ + μ ∈ rootFinset .E8 := by
  simp only [mRoots, lxPos, topsE8, rootFinset_E8_eq]
  decide +kernel

theorem mRoots_height : ∀ μ ∈ mRoots, 0 < height μ ∧ height μ ≤ 29 := by
  simp only [mRoots, rootFinset_E8_eq]
  decide +kernel

theorem add_mem_mRoots : ∀ γ ∈ lxRoots, ∀ μ ∈ mRoots,
    γ + μ ∈ rootFinset .E8 → γ + μ ∈ mRoots := by
  simp only [lxRoots, mRoots, rootFinset_E8_eq]
  decide +kernel

theorem height_sub' (u v : Fin Tag.E8.rank → ℤ) : height (u - v) = height u - height v := by
  simp [height, Finset.sum_sub_distrib]

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
