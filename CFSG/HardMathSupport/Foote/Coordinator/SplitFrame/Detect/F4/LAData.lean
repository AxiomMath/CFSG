module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.RootData
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Frames

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint

@[expose] def s2pos : List (Fin Tag.F4.rank → ℤ) := [![0, 0, 1, 0], ![0, 0, 0, 1], ![0, 0, 1, 1]]

@[expose] def topsOdd : List (Fin Tag.F4.rank → ℤ) := [![1, 1, 2, 2], ![1, 2, 4, 2]]

@[expose] def topsTwo : List (Fin Tag.F4.rank → ℤ) :=
  [![1, 1, 2, 2], ![1, 1, 2, 1], ![1, 2, 4, 2], ![1, 2, 3, 2]]

@[expose] def deg1Roots : List (Fin Tag.F4.rank → ℤ) := mRoots ++ sRoots1

@[expose] def Adm1 (a1 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ) : Prop :=
  ∀ γ ∈ rootFinset .F4, γ 0 = 0 → ∀ μ ∈ deg1Roots,
    (γ + μ ∈ rootFinset .F4 → |a1 γ μ| = if μ - γ ∈ rootFinset .F4 then 2 else 1) ∧
    (γ + μ ∉ rootFinset .F4 → a1 γ μ = 0)

@[expose] def Adm2 (a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ) : Prop :=
  ∀ γ ∈ rootFinset .F4, γ 0 = 0 → ∀ μ ∈ deg1Roots,
    (2 • γ + μ ∈ rootFinset .F4 → |a2 γ μ| = 1) ∧ (2 • γ + μ ∉ rootFinset .F4 → a2 γ μ = 0)

@[expose] def actFun {K : Type} [Field K]
    (a1 a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ) (γ : Fin Tag.F4.rank → ℤ)
    (t : K) (c : (Fin Tag.F4.rank → ℤ) → K) : (Fin Tag.F4.rank → ℤ) → K :=
  fun ν => c ν + t * (a1 γ (ν - γ) : K) * c (ν - γ) +
    t ^ 2 * (a2 γ (ν - 2 • γ) : K) * c (ν - 2 • γ)

theorem f4ShortList_deg0 : ∀ γ ∈ f4ShortList, γ ∈ rootFinset .F4 ∧ γ 0 = 0 := by decide +kernel

theorem Adm1.short {a1 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ} (h : Adm1 a1) :
    ∀ γ ∈ f4ShortList, ∀ μ ∈ deg1Roots,
      (γ + μ ∈ rootFinset .F4 → |a1 γ μ| = if μ - γ ∈ rootFinset .F4 then 2 else 1) ∧
      (γ + μ ∉ rootFinset .F4 → a1 γ μ = 0) := fun γ hγ =>
  h γ (f4ShortList_deg0 γ hγ).1 (f4ShortList_deg0 γ hγ).2

theorem Adm2.short {a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ} (h : Adm2 a2) :
    ∀ γ ∈ f4ShortList, ∀ μ ∈ deg1Roots,
      (2 • γ + μ ∈ rootFinset .F4 → |a2 γ μ| = 1) ∧ (2 • γ + μ ∉ rootFinset .F4 → a2 γ μ = 0) :=
  fun γ hγ => h γ (f4ShortList_deg0 γ hγ).1 (f4ShortList_deg0 γ hγ).2

theorem s2pos_data : ∀ γ ∈ s2pos, γ ∈ f4ShortList ∧ 0 < height γ := by decide +kernel

theorem mRoots_data : ∀ μ ∈ mRoots, μ ∈ rootFinset .F4 ∧ μ 0 = 1 ∧ μ 1 % 3 ≠ 0 := by
  decide +kernel

theorem add_mem_mRoots : ∀ γ ∈ f4ShortList, ∀ μ ∈ mRoots,
    (γ + μ ∈ rootFinset .F4 → γ + μ ∈ mRoots) ∧
    (2 • γ + μ ∈ rootFinset .F4 → 2 • γ + μ ∈ mRoots) := by decide +kernel

theorem non_top_odd : ∀ μ ∈ mRoots, μ ∉ topsOdd → ∃ γ ∈ s2pos, γ + μ ∈ rootFinset .F4 := by
  decide +kernel

theorem non_top_two : ∀ μ ∈ mRoots, μ ∉ topsTwo → ∃ γ ∈ s2pos,
    (γ + μ ∈ rootFinset .F4 ∧ μ - γ ∉ rootFinset .F4) ∨ 2 • γ + μ ∈ rootFinset .F4 := by
  decide +kernel

theorem mRoots_height : ∀ μ ∈ mRoots, 0 < height μ ∧ height μ ≤ 12 := by decide +kernel

theorem height_sub' (u v : Fin Tag.F4.rank → ℤ) : height (u - v) = height u - height v := by
  simp [height, Finset.sum_sub_distrib]

theorem height_two_smul (v : Fin Tag.F4.rank → ℤ) : height (2 • v) = 2 * height v := by
  simp [height, Finset.mul_sum]

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4
