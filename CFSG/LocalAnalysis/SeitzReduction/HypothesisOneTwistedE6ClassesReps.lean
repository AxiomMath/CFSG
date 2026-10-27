module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6TwoBasic

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K]

@[expose] def twistedE6ClassRootU : Fin TwistTag.E6.tag.rank → ℤ :=
  (![1, 1, 1, 2, 2, 1] : Fin 6 → ℤ)

@[expose] def twistedE6ClassRootU' : Fin TwistTag.E6.tag.rank → ℤ :=
  (![1, 1, 2, 2, 1, 1] : Fin 6 → ℤ)

@[expose] def twistedE6ClassRootA : Fin TwistTag.E6.tag.rank → ℤ :=
  (![1, 1, 1, 2, 1, 0] : Fin 6 → ℤ)

@[expose] def twistedE6ClassRootA' : Fin TwistTag.E6.tag.rank → ℤ :=
  (![0, 1, 1, 2, 1, 1] : Fin 6 → ℤ)

@[expose] def twistedE6ClassRootB : Fin TwistTag.E6.tag.rank → ℤ :=
  (![1, 1, 2, 2, 2, 1] : Fin 6 → ℤ)

theorem permLattice_twistedE6ClassRootU :
    permLattice TwistTag.E6.perm twistedE6ClassRootU = twistedE6ClassRootU' := by decide

theorem permLattice_twistedE6ClassRootA :
    permLattice TwistTag.E6.perm twistedE6ClassRootA = twistedE6ClassRootA' := by decide

theorem permLattice_twistedE6ClassRootB :
    permLattice TwistTag.E6.perm twistedE6ClassRootB = twistedE6ClassRootB := by decide

theorem isRoot_twistedE6ClassRoots :
    IsRoot TwistTag.E6.tag twistedE6ClassRootU ∧ IsRoot TwistTag.E6.tag twistedE6ClassRootU' ∧
      IsRoot TwistTag.E6.tag twistedE6ClassRootA ∧ IsRoot TwistTag.E6.tag twistedE6ClassRootA' ∧
        IsRoot TwistTag.E6.tag twistedE6ClassRootB := by
  simp only [isRoot_iff_twistedE6TwoRootB]
  decide +kernel

@[expose] noncomputable def twistedE6ClassU
    (K : Type) [Field K] : ModGL TwistTag.E6.tag K :=
  pinnedX TwistTag.E6.tag K twistedE6ClassRootU 1 * pinnedX TwistTag.E6.tag K twistedE6ClassRootU' 1

@[expose] noncomputable def twistedE6ClassV
    (K : Type) [Field K] : ModGL TwistTag.E6.tag K :=
  pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 *
    pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1 *
      pinnedX TwistTag.E6.tag K twistedE6ClassRootB 1

theorem twistedE6ClassU_eq_twistedE6PairX
    (σ : K →+* K) :
    twistedE6ClassU K = twistedE6PairX σ twistedE6ClassRootU 1 := by
  rw [twistedE6PairX, permLattice_twistedE6ClassRootU, map_one]
  rfl

theorem twistedE6ClassV_eq_twistedE6PairX
    (σ : K →+* K) :
    twistedE6ClassV K = twistedE6PairX σ twistedE6ClassRootA 1 *
      pinnedX TwistTag.E6.tag K twistedE6ClassRootB 1 := by
  rw [twistedE6PairX, permLattice_twistedE6ClassRootA, map_one]
  rfl


theorem pinnedX_mem_graphFixedRootGroup_of_fixed [CharP K 2] (σ : K →+* K)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β)
    (hρ : permLattice TwistTag.E6.perm β = β) {c : K} (hc : σ c = c) :
    pinnedX TwistTag.E6.tag K β c ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  have hΓ : pinnedX TwistTag.E6.tag K β c ∈ twistedFixedGroup TwistTag.E6 K σ := by
    refine (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨pinnedX_mem_adjointGroup _ _, ?_⟩
    rw [twistHom_pinnedX_eq_of_charTwo (CharP.cast_eq_zero K 2) σ hβ, hρ, hc]
  rcases CFSG.LieType.Chevalley.IsRoot.height_pos_or_neg hβ with hp | hn
  · exact graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ (Subgroup.mem_inf.2
      ⟨Subgroup.mem_iSup_of_mem β (Subgroup.mem_iSup_of_mem ⟨hβ, hp⟩
        (mem_rootSubgroup.2 ⟨c, rfl⟩)), hΓ⟩)
  · exact graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _ (Subgroup.mem_inf.2
      ⟨Subgroup.mem_iSup_of_mem β (Subgroup.mem_iSup_of_mem ⟨hβ, hn⟩
        (mem_rootSubgroup.2 ⟨c, rfl⟩)), hΓ⟩)

theorem twistedE6ClassU_mem_graphFixedRootGroup [CharP K 2] {σ : K →+* K}
    (hσσ : ∀ x, σ (σ x) = x) : twistedE6ClassU K ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  rw [twistedE6ClassU_eq_twistedE6PairX σ]
  exact twistedE6PairX_mem_graphFixedRootGroup hσσ isRoot_twistedE6ClassRoots.1 1

theorem twistedE6ClassV_mem_graphFixedRootGroup [CharP K 2] {σ : K →+* K}
    (hσσ : ∀ x, σ (σ x) = x) : twistedE6ClassV K ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  rw [twistedE6ClassV_eq_twistedE6PairX σ]
  exact mul_mem (twistedE6PairX_mem_graphFixedRootGroup hσσ isRoot_twistedE6ClassRoots.2.2.1 1)
    (pinnedX_mem_graphFixedRootGroup_of_fixed σ isRoot_twistedE6ClassRoots.2.2.2.2
      permLattice_twistedE6ClassRootB (map_one σ))

theorem pinnedX_one_sq_of_charTwo [CharP K 2] (ε : Fin TwistTag.E6.tag.rank → ℤ) :
    pinnedX TwistTag.E6.tag K ε 1 ^ 2 = 1 := by
  rw [sq, ← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]

theorem twistedE6ClassU_sq [CharP K 2] : twistedE6ClassU K ^ 2 = 1 := by
  have hc : Commute (pinnedX TwistTag.E6.tag K twistedE6ClassRootU 1)
      (pinnedX TwistTag.E6.tag K twistedE6ClassRootU' 1) := by
    have h := commute_pinnedX_permLattice_twistedE6 (K := K) isRoot_twistedE6ClassRoots.1 1 1
    rwa [permLattice_twistedE6ClassRootU] at h
  rw [twistedE6ClassU, hc.mul_pow, pinnedX_one_sq_of_charTwo, pinnedX_one_sq_of_charTwo, one_mul]

theorem twistedE6ClassV_sq [CharP K 2] : twistedE6ClassV K ^ 2 = 1 := by
  obtain ⟨-, -, hA, hA', hB⟩ := isRoot_twistedE6ClassRoots
  have h1 : Commute (pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1)
      (pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1) := by
    have h := commute_pinnedX_permLattice_twistedE6 (K := K) hA 1 1
    rwa [permLattice_twistedE6ClassRootA] at h
  have hAB : ¬IsRoot TwistTag.E6.tag (twistedE6ClassRootA + twistedE6ClassRootB) := by
    rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel
  have hA'B : ¬IsRoot TwistTag.E6.tag (twistedE6ClassRootA' + twistedE6ClassRootB) := by
    rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel
  have h2 := commute_pinnedX_of_not_isRoot_add_E6 (K := K) hA hB (by decide) (by decide) hAB 1 1
  have h3 := commute_pinnedX_of_not_isRoot_add_E6 (K := K) hA' hB (by decide) (by decide) hA'B 1 1
  rw [twistedE6ClassV, (h2.mul_left h3).mul_pow, h1.mul_pow, pinnedX_one_sq_of_charTwo,
    pinnedX_one_sq_of_charTwo, pinnedX_one_sq_of_charTwo, one_mul, one_mul]

@[expose] def twistedE6ClassReps (K : Type) [Field K] (σ : K →+* K) :
    Set (graphFixedRootGroup TwistTag.E6 K σ) :=
  {c | (c : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∨
    (c : ModGL TwistTag.E6.tag K) = twistedE6ClassU K ∨
      (c : ModGL TwistTag.E6.tag K) = twistedE6ClassV K}

end CFSG.SeitzReduction
