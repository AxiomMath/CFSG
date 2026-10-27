module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootNormalizer
public import CFSG.Blueprint.ChevalleyRootArtifact

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Roots

private theorem not_mem_artifactRoots_single_sub_e6HighestRoot :
    ∀ j : Fin TwistTag.E6.tag.rank, j ≠ 1 →
      List.ofFn (Pi.single j 1 + -e6HighestRoot) ∉ TwistTag.E6.tag.artifactRoots := by
  decide +kernel

private theorem not_mem_artifactRoots_neg_single_sub_e6HighestRoot :
    ∀ j : Fin TwistTag.E6.tag.rank,
      List.ofFn (-Pi.single j 1 + -e6HighestRoot) ∉ TwistTag.E6.tag.artifactRoots := by
  decide +kernel

private theorem single_ne_e6HighestRoot :
    ∀ j : Fin TwistTag.E6.tag.rank, (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) ≠
      e6HighestRoot := by
  decide +kernel

private theorem single_ne_neg_e6HighestRoot :
    ∀ j : Fin TwistTag.E6.tag.rank, (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) ≠
      -e6HighestRoot := by
  decide +kernel

private theorem neg_single_ne_e6HighestRoot :
    ∀ j : Fin TwistTag.E6.tag.rank, (-Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) ≠
      e6HighestRoot := by
  decide +kernel

private theorem ne_one_of_mem_orbitUnion_J0 {j : Fin TwistTag.E6.tag.rank}
    (hj : j ∈ TwistTag.E6.orbitUnion J0) : j ≠ 1 := by
  obtain ⟨a, ha, hja⟩ := (TwistTag.mem_orbitUnion _).1 hj
  rintro rfl
  exact ha (((TwistTag.mem_orbit_iff _).1 hja).symm.trans (by decide))

end Roots

section Levi

variable {K : Type} [Field K]

theorem commute_xUnit_of_mem_rootSubgroup_neg_e6HighestRoot {j : Fin TwistTag.E6.tag.rank}
    (hj : j ≠ 1) (c : K) {y : ModGL TwistTag.E6.tag K}
    (hy : y ∈ rootSubgroup TwistTag.E6.tag K (-e6HighestRoot)) :
    Commute (xUnit TwistTag.E6.tag K j c) y := by
  have hnot : ¬IsRoot TwistTag.E6.tag (Pi.single j 1 + -e6HighestRoot) := fun h =>
    not_mem_artifactRoots_single_sub_e6HighestRoot j hj (isRoot_iff_mem_artifactRoots.1 h)
  have hne' : (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) ≠ - -e6HighestRoot := by
    rw [neg_neg]
    exact single_ne_e6HighestRoot j
  exact (simply_laced_root_commutator_unit TwistTag.E6.tag (Or.inr (Or.inl rfl))
    (isRoot_single _ j) (IsRoot.neg isRoot_e6HighestRoot) (single_ne_neg_e6HighestRoot j) hne').2
    hnot K _ (mem_rootSubgroup.2 ⟨c, pinnedX_single _ _ j c⟩) y hy

theorem commute_yUnit_of_mem_rootSubgroup_neg_e6HighestRoot (j : Fin TwistTag.E6.tag.rank)
    (c : K) {y : ModGL TwistTag.E6.tag K}
    (hy : y ∈ rootSubgroup TwistTag.E6.tag K (-e6HighestRoot)) :
    Commute (yUnit TwistTag.E6.tag K j c) y := by
  have hnot : ¬IsRoot TwistTag.E6.tag (-Pi.single j 1 + -e6HighestRoot) := fun h =>
    not_mem_artifactRoots_neg_single_sub_e6HighestRoot j (isRoot_iff_mem_artifactRoots.1 h)
  have hne : (-Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) ≠ -e6HighestRoot := fun h =>
    single_ne_e6HighestRoot j (neg_inj.1 h)
  have hne' : (-Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) ≠ - -e6HighestRoot := by
    rw [neg_neg]
    exact neg_single_ne_e6HighestRoot j
  exact (simply_laced_root_commutator_unit TwistTag.E6.tag (Or.inr (Or.inl rfl))
    (isRoot_neg_single _ j) (IsRoot.neg isRoot_e6HighestRoot) hne hne').2
    hnot K _ (mem_rootSubgroup.2 ⟨c, pinnedX_neg_single _ _ j c⟩) y hy

theorem parabolicLevi_le_normalizer_rootSubgroup_neg_e6HighestRoot :
    parabolicLevi TwistTag.E6.tag K (TwistTag.E6.orbitUnion J0) ≤
      Subgroup.normalizer
        (rootSubgroup TwistTag.E6.tag K (-e6HighestRoot) : Set (ModGL TwistTag.E6.tag K)) := by
  refine sup_le (torusGroup_le_normalizer_rootSubgroup (IsRoot.neg isRoot_e6HighestRoot)) ?_
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨j, hj, c, rfl | rfl⟩
  · refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun y hy => ?_)
    exact (commute_xUnit_of_mem_rootSubgroup_neg_e6HighestRoot (ne_one_of_mem_orbitUnion_J0 hj) c
      hy).symm.eq
  · refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun y hy => ?_)
    exact (commute_yUnit_of_mem_rootSubgroup_neg_e6HighestRoot j c hy).symm.eq

variable [Finite K] (σ : K ≃+* K)

theorem graphFixedParabolicLevi_subgroupOf_le_normalizer :
    (graphFixedParabolicLevi TwistTag.E6 K σ.toRingHom J0).subgroupOf (twistedE6RootGroup K σ) ≤
      Subgroup.normalizer
        (twE6RootSubgroup K σ (-e6HighestRoot) : Set (twistedE6RootGroup K σ)) := by
  intro g hg
  exact mem_normalizer_comap_of_coe_mem_normalizer _
    (parabolicLevi_le_normalizer_rootSubgroup_neg_e6HighestRoot
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hg)).1)

end Levi

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot
