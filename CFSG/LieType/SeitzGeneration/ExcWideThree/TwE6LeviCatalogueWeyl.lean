module

public import CFSG.LieType.Chevalley.E6GraphLeviRealization
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalOpposite
public import CFSG.LieType.Chevalley.KernelComponentRoots

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphHighestRoot CFSG.LieType.Chevalley.EvenOddRadical

section Radical

private theorem aux_sub_mem :
    ∀ α ∈ rootFinset TwistTag.E6.tag, 0 < height α → α (e6Idx 1) ≠ 0 →
      (α (e6Idx 1) • e6HighestRoot - α) ∈ rootFinset TwistTag.E6.tag ∧
        0 < height (α (e6Idx 1) • e6HighestRoot - α) ∧
        (α (e6Idx 1) • e6HighestRoot - α) (e6Idx 1) ≠ 0 := by
  decide +kernel

theorem mem_parabolicRadicalRoots_setA_iff {α : Fin TwistTag.E6.tag.rank → ℤ} :
    α ∈ parabolicRadicalRoots TwistTag.E6.tag E6GraphLevi.setA ↔
      IsRoot TwistTag.E6.tag α ∧ 0 < height α ∧ α (e6Idx 1) ≠ 0 := by
  rw [mem_parabolicRadicalRoots_iff]
  refine and_congr_right fun _ => and_congr_right fun _ =>
    ⟨?_, fun h => ⟨e6Idx 1, fun h' => h' rfl, h⟩⟩
  rintro ⟨i, hi, h⟩
  have : i = e6Idx 1 := by
    by_contra h'
    exact hi h'
  exact this ▸ h

end Radical

section Lattice

theorem rootReflection_e6HighestRoot_smul (v : Fin TwistTag.E6.tag.rank → ℤ) :
    rootReflection e6HighestRoot • v = v - v (e6Idx 1) • e6HighestRoot := by
  rw [rootReflection_smul isRoot_e6HighestRoot, corootPair, iform_e6HighestRoot,
    iform_e6HighestRoot, show e6HighestRoot (e6Idx 1) = 2 from rfl,
    Int.mul_ediv_cancel_left _ two_ne_zero]

theorem rootReflection_e6HighestRoot_smul_self :
    rootReflection e6HighestRoot • e6HighestRoot = -e6HighestRoot :=
  rootReflection_smul_self isRoot_e6HighestRoot

theorem rootReflection_e6HighestRoot_smul_single {i : Fin TwistTag.E6.tag.rank}
    (hi : i ∈ E6GraphLevi.setA) :
    rootReflection e6HighestRoot • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) =
      Pi.single i 1 := by
  rw [rootReflection_e6HighestRoot_smul]
  have : (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) (e6Idx 1) = 0 :=
    Pi.single_eq_of_ne (fun h => hi h.symm) _
  rw [this, zero_smul, sub_zero]

theorem rootReflection_e6HighestRoot_smul_neg_single {i : Fin TwistTag.E6.tag.rank}
    (hi : i ∈ E6GraphLevi.setA) :
    rootReflection e6HighestRoot • (-Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) =
      -Pi.single i 1 := by
  rw [smul_neg, rootReflection_e6HighestRoot_smul_single hi]

theorem neg_rootReflection_e6HighestRoot_smul_mem_parabolicRadicalRoots
    {α : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : α ∈ parabolicRadicalRoots TwistTag.E6.tag E6GraphLevi.setA) :
    -(rootReflection e6HighestRoot • α) ∈
      parabolicRadicalRoots TwistTag.E6.tag E6GraphLevi.setA := by
  obtain ⟨hr, hp, h1⟩ := mem_parabolicRadicalRoots_setA_iff.1 hα
  obtain ⟨h2, h3, h4⟩ := aux_sub_mem α (mem_rootFinset.2 hr) hp h1
  rw [mem_parabolicRadicalRoots_setA_iff]
  have e : -(rootReflection e6HighestRoot • α) = α (e6Idx 1) • e6HighestRoot - α := by
    rw [rootReflection_e6HighestRoot_smul]
    abel
  rw [e]
  exact ⟨mem_rootFinset.1 h2, h3, h4⟩

end Lattice

section Transport

variable (K : Type) [Field K]

@[expose] def twE6LeviN0 : ModGL TwistTag.E6.tag K :=
  canonicalRep (coxeterSystem TwistTag.E6.tag) K (rootReflection e6HighestRoot)

theorem map_conj_twE6LeviN0_rootSubgroup_e6HighestRoot :
    (rootSubgroup TwistTag.E6.tag K e6HighestRoot).map (MulAut.conj (twE6LeviN0 K)).toMonoidHom =
      rootSubgroup TwistTag.E6.tag K (-e6HighestRoot) := by
  have h := (canonical_weyl_root_transport TwistTag.E6.tag K).2.1 (rootReflection e6HighestRoot)
    e6HighestRoot isRoot_e6HighestRoot
  rw [rootReflection_e6HighestRoot_smul_self] at h
  exact h

theorem map_conj_twE6LeviN0_parabolicRadical_le_oppRadical :
    (parabolicRadical TwistTag.E6.tag K E6GraphLevi.setA).map
        (MulAut.conj (twE6LeviN0 K)).toMonoidHom ≤
      oppRadical TwistTag.E6.tag K E6GraphLevi.setA := by
  have hT := (canonical_weyl_root_transport TwistTag.E6.tag K).1 (rootReflection e6HighestRoot)
    (parabolicRadicalRoots TwistTag.E6.tag E6GraphLevi.setA) (fun α hα => hα.1.1)
  rw [parabolicRadical, oppRadical]
  refine le_of_eq_of_le hT (rootSpan_mono ?_)
  rintro _ ⟨α, hα, rfl⟩
  exact neg_rootReflection_e6HighestRoot_smul_mem_parabolicRadicalRoots hα

theorem map_conj_twE6LeviN0_parabolicLevi_le :
    (parabolicLevi TwistTag.E6.tag K E6GraphLevi.setA).map
        (MulAut.conj (twE6LeviN0 K)).toMonoidHom ≤
      parabolicLevi TwistTag.E6.tag K E6GraphLevi.setA := by
  rw [parabolicLevi, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨t, ht, rfl⟩
    have hn := (canonical_weyl_root_transport TwistTag.E6.tag K).2.2 (rootReflection e6HighestRoot)
    exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 hn t).1 ht)
  · rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨j, hj, c, rfl | rfl⟩, rfl⟩
    · have h := (canonical_weyl_root_transport TwistTag.E6.tag K).2.1
        (rootReflection e6HighestRoot) (Pi.single j 1) (isRoot_single _ j)
      rw [rootReflection_e6HighestRoot_smul_single hj] at h
      have hmem : (MulAut.conj (twE6LeviN0 K)).toMonoidHom (xUnit TwistTag.E6.tag K j c) ∈
          rootSubgroup TwistTag.E6.tag K (Pi.single j 1) := by
        rw [← h]
        exact Subgroup.mem_map_of_mem _ (mem_rootSubgroup.2 ⟨c, pinnedX_single _ _ _ _⟩)
      obtain ⟨c', hc'⟩ := mem_rootSubgroup.1 hmem
      rw [pinnedX_single] at hc'
      rw [← hc']
      exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨j, hj, c', Or.inl rfl⟩)
    · have h := (canonical_weyl_root_transport TwistTag.E6.tag K).2.1
        (rootReflection e6HighestRoot) (-Pi.single j 1) (isRoot_neg_single _ j)
      rw [rootReflection_e6HighestRoot_smul_neg_single hj] at h
      have hmem : (MulAut.conj (twE6LeviN0 K)).toMonoidHom (yUnit TwistTag.E6.tag K j c) ∈
          rootSubgroup TwistTag.E6.tag K (-Pi.single j 1) := by
        rw [← h]
        exact Subgroup.mem_map_of_mem _ (mem_rootSubgroup.2 ⟨c, pinnedX_neg_single _ _ _ _⟩)
      obtain ⟨c', hc'⟩ := mem_rootSubgroup.1 hmem
      rw [pinnedX_neg_single] at hc'
      rw [← hc']
      exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨j, hj, c', Or.inr rfl⟩)

end Transport

end CFSG.LieType.SeitzGeneration.ExcWideThree
