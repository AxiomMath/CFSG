module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux13
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux19
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenData5

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
open scoped commutatorElement

set_option linter.unusedSectionVars false


section T3

variable {K : Type} [Field K] [Finite K] (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w)

theorem ΨE_Uneg {u : ModGL Tag.E8 K} (hu : u ∈ Heis.Uneg Tag.E8 K) :
    ∃ t : D.L, ΨE D u = pinnedX Tag.E8 D.L (-highRoot Tag.E8) t := by
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hu
  have hbc : baseChangeGL (algebraMap K D.L) (pinnedX Tag.E8 K (-highRoot Tag.E8) c) =
      pinnedX Tag.E8 D.L (-highRoot Tag.E8) (algebraMap K D.L c) := baseChangeGL_pinnedX _ _ _
  have hx : pinnedX Tag.E8 D.L (-highRoot Tag.E8) (algebraMap K D.L c) ∈ Heis.Uneg Tag.E8 D.L :=
    mem_rootSubgroup.2 ⟨_, rfl⟩
  have hinv : (gE D)⁻¹ ∈ Lθ Tag.E8 D.L := inv_mem (gE_mem_Lθ D)
  have hmem := (Subgroup.mem_normalizer_iff.1 (Lθ_le_normalizer_Uneg Tag.E8 D.L hinv)
    (pinnedX Tag.E8 D.L (-highRoot Tag.E8) (algebraMap K D.L c))).1 hx
  rw [inv_inv] at hmem
  obtain ⟨t, ht⟩ := mem_rootSubgroup.1 hmem
  refine ⟨t, ?_⟩
  unfold ΨE
  rw [hbc, ht]

theorem exists_T3 (hK : Nat.card K = 2) :
    ∃ ℓ : ModGL Tag.E8 K, ℓ ∈ TwClass.e8Ten.X₁ D ∧ ∃ c d z : D.L, c ≠ 0 ∧ d ≠ 0 ∧
      ΨE D ℓ = pinnedX Tag.E8 D.L vA6 c * pinnedX Tag.E8 D.L vA7 d * pinnedX Tag.E8 D.L vGc z := by
  haveI hAC : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  set S := toSetup D ⊥ with hS
  have ht : ((Pi.single 5 1 : Fin Tag.E8.rank → ℤ), (Pi.single 6 1 : Fin Tag.E8.rank → ℤ),
      (Pi.single 5 1 + Pi.single 6 1 : Fin Tag.E8.rank → ℤ)) ∈ a2Triples := by
    simp [a2Triples]
  obtain ⟨h1, h2, h3, hw1, hw2, hw3, hsum, hne, hne', h31, h32, n31, n31', n32, n32'⟩ :=
    a2Triples_data _ ht
  obtain ⟨hr1, h01, -⟩ := lxRoots_data _ h1
  obtain ⟨hr2, h02, -⟩ := lxRoots_data _ h2
  obtain ⟨hr3, h03, -⟩ := lxRoots_data _ h3
  obtain ⟨η, hη⟩ := pinnedX_A2_rel (R := D.L) hr1 hr2 hsum.symm hr3 hne hne' h31 h32 n31 n31'
    n32 n32'
  obtain ⟨hs₁, hc₁⟩ := S.hm _ (mem_rootFinset.1 hr1)
  obtain ⟨hs₂, hc₂⟩ := S.hm _ (mem_rootFinset.1 hr2)
  obtain ⟨hs₃, hc₃⟩ := S.hm _ (mem_rootFinset.1 hr3)
  obtain ⟨c, d, hc0, hFc, hFd⟩ := S.exists_pair (mem_rootFinset.1 hr1) (mem_rootFinset.1 hr2)
  obtain ⟨z, hz⟩ := exists_AS (K := K) (S.sg_ne_zero (mem_rootFinset.1 hr3)) (η * c * d)
  have hw1' : S.w • (Pi.single 5 1 : Fin Tag.E8.rank → ℤ) = Pi.single 6 1 := by
    rw [toSetup_hw]
    exact hw1
  have hw2' : S.w • (Pi.single 6 1 : Fin Tag.E8.rank → ℤ) = Pi.single 5 1 := by
    rw [toSetup_hw]
    exact hw2
  have hw3' : S.w • (Pi.single 5 1 + Pi.single 6 1 : Fin Tag.E8.rank → ℤ) =
      Pi.single 5 1 + Pi.single 6 1 := by
    rw [toSetup_hw]
    exact hw3
  have hσ : S.n * Frob S.Fr (pinnedX Tag.E8 D.L (Pi.single 5 1) c *
      pinnedX Tag.E8 D.L (Pi.single 6 1) d *
      pinnedX Tag.E8 D.L (Pi.single 5 1 + Pi.single 6 1) z) * S.n⁻¹ =
      pinnedX Tag.E8 D.L (Pi.single 5 1) c * pinnedX Tag.E8 D.L (Pi.single 6 1) d *
      pinnedX Tag.E8 D.L (Pi.single 5 1 + Pi.single 6 1) z := by
    have e : S.n * (pinnedX Tag.E8 D.L (Pi.single 5 1) (S.Fr c) *
        pinnedX Tag.E8 D.L (Pi.single 6 1) (S.Fr d) *
        pinnedX Tag.E8 D.L (Pi.single 5 1 + Pi.single 6 1) (S.Fr z)) * S.n⁻¹ =
        (S.n * pinnedX Tag.E8 D.L (Pi.single 5 1) (S.Fr c) * S.n⁻¹) *
          (S.n * pinnedX Tag.E8 D.L (Pi.single 6 1) (S.Fr d) * S.n⁻¹) *
          (S.n * pinnedX Tag.E8 D.L (Pi.single 5 1 + Pi.single 6 1) (S.Fr z) * S.n⁻¹) := by group
    rw [map_mul, map_mul, Frob_pinnedX, Frob_pinnedX, Frob_pinnedX, e, hc₁ (S.Fr c),
      hc₂ (S.Fr d), hc₃ (S.Fr z), hw1', hw2', hw3', hFc, hFd, hη d c,
      mul_assoc (pinnedX Tag.E8 D.L (Pi.single 5 1) c * pinnedX Tag.E8 D.L (Pi.single 6 1) d),
      ← pinnedX_add]
    have hzz : η * d * c + S.sg (Pi.single 5 1 + Pi.single 6 1) * S.Fr z = z := by
      rw [S.hFr z]
      linear_combination (-1 : D.L) * hz
    rw [hzz]
  have hxA : pinnedX Tag.E8 D.L (Pi.single 5 1) c * pinnedX Tag.E8 D.L (Pi.single 6 1) d *
      pinnedX Tag.E8 D.L (Pi.single 5 1 + Pi.single 6 1) z ∈ adjointGroup Tag.E8 D.L :=
    mul_mem (mul_mem (rootSubgroup_le_adjointGroup _ (mem_rootSubgroup.2 ⟨c, rfl⟩))
      (rootSubgroup_le_adjointGroup _ (mem_rootSubgroup.2 ⟨d, rfl⟩)))
      (rootSubgroup_le_adjointGroup _ (mem_rootSubgroup.2 ⟨z, rfl⟩))
  obtain ⟨l, hlA, hl⟩ := S.rat_of_sfixed hxA hσ
  have hl' : baseChangeGL (algebraMap K D.L) l = gE D * (pinnedX Tag.E8 D.L (Pi.single 5 1) c *
      pinnedX Tag.E8 D.L (Pi.single 6 1) d *
      pinnedX Tag.E8 D.L (Pi.single 5 1 + Pi.single 6 1) z) * (gE D)⁻¹ := hl
  have hΨ : ΨE D l = pinnedX Tag.E8 D.L (Pi.single 5 1) c * pinnedX Tag.E8 D.L (Pi.single 6 1) d *
      pinnedX Tag.E8 D.L (Pi.single 5 1 + Pi.single 6 1) z := by
    unfold ΨE
    rw [hl']
    group
  have hd0 : d ≠ 0 := by
    rw [← hFc]
    exact mul_ne_zero (S.sg_ne_zero (mem_rootFinset.1 hr1)) (by
      rw [S.hFr c]
      exact pow_ne_zero _ hc0)
  refine ⟨l, ?_, c, d, z, hc0, hd0, hΨ⟩
  refine (mem_frame_iff' D TwClass.e8Ten.S₁ l).2 ⟨hlA, ?_⟩
  have h1' : ΨE D l ∈ rootSpan Tag.E8 D.L TwClass.e8Ten.S₁ := by
    rw [hΨ]
    refine mul_mem (mul_mem ?_ ?_) ?_
    · exact pinnedX_mem_S₁ D (s1_data (Pi.single 5 1) (by simp)).1
        (s1_data (Pi.single 5 1) (by simp)).2 c
    · exact pinnedX_mem_S₁ D (s1_data (Pi.single 6 1) (by simp)).1
        (s1_data (Pi.single 6 1) (by simp)).2 d
    · exact pinnedX_mem_S₁ D (s1_data (Pi.single 5 1 + Pi.single 6 1) (by simp)).1
        (s1_data (Pi.single 5 1 + Pi.single 6 1) (by simp)).2 z
  exact h1'

end T3

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
