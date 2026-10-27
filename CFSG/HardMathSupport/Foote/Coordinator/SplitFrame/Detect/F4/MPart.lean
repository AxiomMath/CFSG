module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.Transport
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.LAData
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Coordinates

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint Heis

set_option linter.unusedSectionVars false


variable (K : Type) [Field K]

@[expose] def MElement (q : ModGL Tag.F4 K) : Prop := ∃ β ∈ mRoots, heisCoord Tag.F4 K q β ≠ 0

@[expose] def MPart (H : Subgroup (ModGL Tag.F4 K)) : Prop :=
  ∃ q ∈ H, q ∈ Qθ Tag.F4 K ∧ MElement K q

theorem deg1_iff {β : Fin Tag.F4.rank → ℤ} :
    β ∈ Deg1 Tag.F4 ↔ IsRoot Tag.F4 β ∧ β 0 = 1 := Iff.rfl

theorem mem_Deg1_of_mem_deg1Roots {β : Fin Tag.F4.rank → ℤ} (h : β ∈ deg1Roots) :
    β ∈ Deg1 Tag.F4 := by
  have : ∀ β ∈ deg1Roots, β ∈ rootFinset .F4 ∧ β 0 = 1 := by decide +kernel
  exact ⟨mem_rootFinset.1 (this β h).1, (this β h).2⟩

theorem mem_deg1Roots_of_mem_Deg1 {β : Fin Tag.F4.rank → ℤ} (h : β ∈ Deg1 Tag.F4) :
    β ∈ deg1Roots := by
  have h1 : ∀ β ∈ rootFinset .F4, β 0 = 1 → β ∈ deg1Roots := by decide +kernel
  exact h1 β (mem_rootFinset.2 h.1) h.2

theorem pinnedX_mem_Qθ {β : Fin Tag.F4.rank → ℤ} (hβ : β ∈ Deg1 Tag.F4) (c : K) :
    pinnedX Tag.F4 K β c ∈ Qθ Tag.F4 K := by
  refine pinnedX_mem_rootSpan ?_ c
  have h0 : β (Heis.iθ Tag.F4) = 1 := hβ.2
  rw [mem_parabolicRadicalRoots_iff]
  refine ⟨hβ.1, ?_, Heis.iθ Tag.F4, fun h => ?_, ?_⟩
  · rcases IsRoot.height_pos_or_neg hβ.1 with hp | hn
    · exact hp
    · exfalso
      have := (IsRoot.height_neg_iff hβ.1).1 hn (Heis.iθ Tag.F4)
      omega
  · exact h rfl
  · omega

theorem Uθ_le_Qθ : Uθ Tag.F4 K ≤ Qθ Tag.F4 K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  refine pinnedX_mem_rootSpan ?_ c
  rw [mem_parabolicRadicalRoots_iff]
  refine ⟨isRoot_theta, ?_, Heis.iθ Tag.F4, fun h => h rfl, ?_⟩
  · exact height_highRoot_pos Tag.F4
  · decide +kernel

theorem Uθ_le_X1 : Uθ Tag.F4 K ≤ X1 K := rootSubgroup_le_rootSpan_aux theta_mem_S1set K

theorem Uneg_le_X1 : Heis.Uneg Tag.F4 K ≤ X1 K := rootSubgroup_le_rootSpan_aux neg_theta_mem_S1set K

theorem alpha1_deg1 : alpha1 ∈ Deg1 Tag.F4 := ⟨isRoot_alpha1, by decide +kernel⟩

theorem root1342_deg1 : root1342 ∈ Deg1 Tag.F4 := ⟨isRoot_root1342, by decide +kernel⟩

theorem alpha1_ne_root1342 : alpha1 ≠ root1342 := by decide +kernel

theorem Deg1_cases {β : Fin Tag.F4.rank → ℤ} (h : β ∈ Deg1 Tag.F4) :
    β = alpha1 ∨ β = root1342 ∨ β ∈ mRoots := by
  have hh : ∀ β ∈ deg1Roots, β = alpha1 ∨ β = root1342 ∨ β ∈ mRoots := by decide +kernel
  exact hh β (mem_deg1Roots_of_mem_Deg1 h)

theorem mem_X1_of_coord_M_zero {q : ModGL Tag.F4 K} (hq : q ∈ Qθ Tag.F4 K)
    (h : ∀ β ∈ mRoots, heisCoord Tag.F4 K q β = 0) : q ∈ X1 K := by
  classical
  have hs := heisCoord_spec Tag.F4 K
  set c₁ := heisCoord Tag.F4 K q alpha1 with hc₁
  set c₂ := heisCoord Tag.F4 K q root1342 with hc₂
  have hp1 := pinnedX_mem_Qθ K alpha1_deg1 c₁
  have hp2 := pinnedX_mem_Qθ K root1342_deg1 c₂
  have hsQ : pinnedX Tag.F4 K alpha1 c₁ * pinnedX Tag.F4 K root1342 c₂ ∈ Qθ Tag.F4 K :=
    mul_mem hp1 hp2
  have hcs : heisCoord Tag.F4 K (pinnedX Tag.F4 K alpha1 c₁ * pinnedX Tag.F4 K root1342 c₂) =
      Pi.single alpha1 c₁ + Pi.single root1342 c₂ := by
    rw [hs.mul _ hp1 _ hp2, hs.pinnedX_deg1 alpha1 alpha1_deg1 c₁,
      hs.pinnedX_deg1 root1342 root1342_deg1 c₂]
  have hzero : heisCoord Tag.F4 K
      (q * (pinnedX Tag.F4 K alpha1 c₁ * pinnedX Tag.F4 K root1342 c₂)⁻¹) = 0 := by
    rw [hs.mul q hq _ (inv_mem hsQ), heisCoord_inv hsQ, hcs]
    funext ν
    simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply]
    by_cases h1 : ν = alpha1
    · subst h1
      rw [Pi.single_eq_same, Pi.single_eq_of_ne alpha1_ne_root1342]
      simp [hc₁]
    · by_cases h2 : ν = root1342
      · subst h2
        rw [Pi.single_eq_of_ne (Ne.symm alpha1_ne_root1342), Pi.single_eq_same]
        simp [hc₂]
      · rw [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]
        by_cases hD : ν ∈ Deg1 Tag.F4
        · rcases Deg1_cases hD with h3 | h3 | h3
          · exact absurd h3 h1
          · exact absurd h3 h2
          · simp [h ν h3]
        · simp [hs.support q hq ν hD]
  have hU := (hs.eq_zero_iff _ (mul_mem hq (inv_mem hsQ))).1 hzero
  have hq' : q = (q * (pinnedX Tag.F4 K alpha1 c₁ * pinnedX Tag.F4 K root1342 c₂)⁻¹) *
      (pinnedX Tag.F4 K alpha1 c₁ * pinnedX Tag.F4 K root1342 c₂) := by group
  rw [hq']
  refine mul_mem (Uθ_le_X1 K hU) (mul_mem ?_ ?_)
  · exact pinnedX_mem_rootSpan alpha1_mem_S1set c₁
  · exact pinnedX_mem_rootSpan root1342_mem_S1set c₂

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4
