module

public import CFSG.LieType.Chevalley.ParabolicRadicalLevi

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

variable {τ : Tag} {K : Type} [Field K]

variable (τ K) in
@[expose] def rootLevi
    (J : Set (Fin τ.rank)) : Subgroup (ModGL τ K) :=
  rootSpan τ K (parabolicRoots τ J)

theorem parabolicDegree_eq_zero_of_mem_parabolicRoots {J : Set (Fin τ.rank)}
    {α : Fin τ.rank → ℤ} (hα : α ∈ parabolicRoots τ J) : parabolicDegree τ J α = 0 :=
  Finset.sum_eq_zero fun i _ => by
    split_ifs with hi
    · rfl
    · exact hα.2 i hi

theorem pinnedX_mem_graded
    {J : Set (Fin τ.rank)} {α : Fin τ.rank → ℤ}
    (hα : α ∈ parabolicRoots τ J) (c : K) {d : ℤ} {x : RootModule τ K}
    (hx : x ∈ parabolicGraded τ K J d) :
    (pinnedX τ K α c : Module.End K (RootModule τ K)) x ∈ parabolicGraded τ K J d := by
  rw [pinnedX_eq_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pinnedCoeff_zero]
    exact hx
  · refine mem_graded_of_mapsLabelWt (mapsLabelWt_pinnedCoeff hα.1 hk) ?_ hx
    rw [parabolicDegree_nsmul, parabolicDegree_eq_zero_of_mem_parabolicRoots hα, mul_zero]

theorem rootLevi_preserves
    {J : Set (Fin τ.rank)} {g : ModGL τ K} (hg : g ∈ rootLevi τ K J)
    (d : ℤ) {x : RootModule τ K} (hx : x ∈ parabolicGraded τ K J d) :
    (g : Module.End K (RootModule τ K)) x ∈ parabolicGraded τ K J d := by
  have hL : rootLevi τ K J = Subgroup.closure
      (⋃ α ∈ parabolicRoots τ J, Set.range (pinnedX τ K α)) := by
    simp only [rootLevi, rootSpan, rootSubgroup, Subgroup.closure_iUnion]
  rw [hL] at hg
  induction hg using Subgroup.closure_induction'' generalizing x with
  | mem g hgs =>
    obtain ⟨α, hα, c, rfl⟩ := by simpa using hgs
    exact pinnedX_mem_graded hα c hx
  | inv_mem g hgs =>
    obtain ⟨α, hα, c, rfl⟩ := by simpa using hgs
    rw [pinnedX_neg]
    exact pinnedX_mem_graded hα (-c) hx
  | one => simpa using hx
  | mul g h _ _ hg hh =>
    rw [Units.val_mul, Module.End.mul_apply]
    exact hg (hh hx)

theorem eq_one_of_mem_parabolicRadical_of_preserves
    {J : Set (Fin τ.rank)} {g : ModGL τ K}
    (hgQ : g ∈ parabolicRadical τ K J)
    (hgV : ∀ (d : ℤ) (x : RootModule τ K), x ∈ parabolicGraded τ K J d →
      (g : Module.End K (RootModule τ K)) x ∈ parabolicGraded τ K J d) : g = 1 := by
  refine Units.ext (end_ext_single fun b => ?_)
  set d := parabolicDegree τ J (labelWt τ b)
  have hbV : (Finsupp.single b 1 : RootModule τ K) ∈ parabolicGraded τ K J d := by
    rw [parabolicGraded_eq_supported]
    exact Finsupp.single_mem_supported K 1 rfl
  have hbF : (Finsupp.single b 1 : RootModule τ K) ∈ parabolicFiltration τ K J d := by
    rw [parabolicFiltration_eq_supported]
    exact Finsupp.single_mem_supported K 1 (show d ≤ d from le_rfl)
  have h1 := hgV d _ hbV
  have h2 := (parabolicRadical_unipotent hgQ d hbF).2
  have h3 : (g : Module.End K (RootModule τ K)) (Finsupp.single b 1) - Finsupp.single b 1 ∈
      parabolicGraded τ K J d ⊓ parabolicFiltration τ K J (d + 1) :=
    Submodule.mem_inf.2 ⟨Submodule.sub_mem _ h1 hbV, h2⟩
  rw [parabolicGraded_inf_filtration_succ, Submodule.mem_bot, sub_eq_zero] at h3
  rw [h3, Units.val_one, Module.End.one_apply]

theorem large_Ree_parabolic_degree_intersection
    (τ : Tag) (K : Type) [Field K]
    (J : Set (Fin τ.rank)) :
    rootLevi τ K J ⊓ parabolicRadical τ K J = ⊥ ∧
    (∀ g ∈ rootLevi τ K J ⊓ borelGroup τ K,
      g ∈ (torusGroup τ K : Set (ModGL τ K)) *
        (parabolicLeviUnipotent τ K J : Set (ModGL τ K))) ∧
    (∀ g ∈ rootLevi τ K J, ∀ (d : ℤ) (x : RootModule τ K), x ∈ parabolicGraded τ K J d →
      (g : Module.End K (RootModule τ K)) x ∈ parabolicGraded τ K J d) ∧
    (∀ g ∈ torusGroup τ K, ∀ (d : ℤ) (x : RootModule τ K), x ∈ parabolicGraded τ K J d →
      (g : Module.End K (RootModule τ K)) x ∈ parabolicGraded τ K J d) ∧
    ∀ u ∈ parabolicRadical τ K J, ∀ (d : ℤ) (x : RootModule τ K),
      x ∈ parabolicGraded τ K J d →
        (u : Module.End K (RootModule τ K)) x - x ∈ parabolicFiltration τ K J (d + 1) := by
  have hT : ∀ g ∈ torusGroup τ K, ∀ (d : ℤ) (x : RootModule τ K),
      x ∈ parabolicGraded τ K J d →
        (g : Module.End K (RootModule τ K)) x ∈ parabolicGraded τ K J d := fun g hg d x hx =>
    parabolicLevi_preserves (torusGroup_le_parabolicLevi J hg) d hx
  have hVF : ∀ d, parabolicGraded τ K J d ≤ parabolicFiltration τ K J d := fun d =>
    (le_iSup₂_of_le d le_rfl le_rfl : parabolicGraded τ K J d ≤ parabolicFiltration τ K J d)
  refine ⟨eq_bot_iff.2 fun g hg => ?_, fun g hg => ?_,
    fun g hg d x hx => rootLevi_preserves hg d hx, hT,
    fun u hu d x hx => (parabolicRadical_unipotent hu d (hVF d hx)).2⟩
  · obtain ⟨hgL, hgQ⟩ := Subgroup.mem_inf.1 hg
    exact Subgroup.mem_bot.2 (eq_one_of_mem_parabolicRadical_of_preserves hgQ
      fun d x hx => rootLevi_preserves hgL d hx)
  · obtain ⟨hgL, hgB⟩ := Subgroup.mem_inf.1 hg
    have hg' : g ∈ (parabolicRadical τ K J : Set (ModGL τ K)) *
        ((torusGroup τ K : Set (ModGL τ K)) *
          (parabolicLeviUnipotent τ K J : Set (ModGL τ K))) := by
      rw [← borelGroup_eq_mul_parabolic]
      exact hgB
    obtain ⟨q, hq, _, ⟨h, hh, v, hv, rfl⟩, rfl⟩ := hg'
    have hm : h * v ∈ parabolicLevi τ K J :=
      mul_mem (torusGroup_le_parabolicLevi J hh) (parabolicLeviUnipotent_le_parabolicLevi J hv)
    have hq1 : q = 1 := by
      refine eq_one_of_mem_parabolicRadical_of_preserves hq fun d x hx => ?_
      have hx' := parabolicLevi_preserves (inv_mem hm) d hx
      have := rootLevi_preserves hgL d hx'
      rwa [Units.val_mul, Module.End.mul_apply, ← Module.End.mul_apply (f := ((h * v : ModGL τ K) :
        Module.End K (RootModule τ K))), ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Module.End.one_apply] at this
    subst hq1
    exact ⟨h, hh, v, hv, by simp⟩

end CFSG.LieType.Chevalley
