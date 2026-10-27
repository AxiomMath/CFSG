module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6C4Gens

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.Timmesfeld CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Chevalley.E6SignedGraph
open CFSG.ClassicalInvolution.WeakCT (range_le_of_tv)
open scoped MatrixGroups Matrix commutatorElement

variable {K : Type} [Field K]

theorem commute_e6C4Rho_zero_three
    (A B : SL(2, K)) : Commute (e6C4Rho K 0 A) (e6C4Rho K 3 B) := by
  obtain ⟨ha, hb, -, -⟩ := e6C4_roots
  have he := isRoot_single TwistTag.E6.tag ⟨3, by decide⟩
  have hA : e6C4Rho K 0 A ∈ Subgroup.closure
      (Set.range (pinnedX TwistTag.E6.tag K (simpleRoot 0)) ∪
        Set.range (pinnedX TwistTag.E6.tag K (rho (simpleRoot 0))) ∪
        Set.range (pinnedX TwistTag.E6.tag K (-simpleRoot 0)) ∪
        Set.range (pinnedX TwistTag.E6.tag K (-rho (simpleRoot 0)))) := by
    refine range_le_of_tv _ _ (fun c => ?_) (fun c => ?_) ⟨A, rfl⟩
    · obtain ⟨⟨t₁, t₂, h⟩, -⟩ := e6C4Rho_zero_gens (K := K) c
      rw [h]
      exact mul_mem (Subgroup.subset_closure (Or.inl (Or.inl (Or.inl ⟨t₁, rfl⟩))))
        (Subgroup.subset_closure (Or.inl (Or.inl (Or.inr ⟨t₂, rfl⟩))))
    · obtain ⟨-, ⟨t₁, t₂, h⟩⟩ := e6C4Rho_zero_gens (K := K) c
      rw [h]
      exact mul_mem (Subgroup.subset_closure (Or.inl (Or.inr ⟨t₁, rfl⟩)))
        (Subgroup.subset_closure (Or.inr ⟨t₂, rfl⟩))
  have hB : e6C4Rho K 3 B ∈ Subgroup.closure
      (Set.range (pinnedX TwistTag.E6.tag K (Pi.single ⟨3, by decide⟩ 1)) ∪
        Set.range (pinnedX TwistTag.E6.tag K (-Pi.single ⟨3, by decide⟩ 1))) := by
    rw [(e6C4Rho_eq_e6F4Rho K).2.2]
    refine range_le_of_tv _ _ (fun c => ?_) (fun c => ?_) ⟨B, rfl⟩
    · change simpleRootSL2 TwistTag.E6.tag K ⟨3, by decide⟩ (tv 0 1 c) ∈ _
      rw [simpleRootSL2_tv01, ← pinnedX_single]
      exact Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)
    · change simpleRootSL2 TwistTag.E6.tag K ⟨3, by decide⟩ (tv 1 0 c) ∈ _
      rw [simpleRootSL2_tv10, ← pinnedX_neg_single]
      exact Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)
  refine commute_of_mem_closure ?_ hA hB
  rintro _ (((⟨c, rfl⟩ | ⟨c, rfl⟩) | ⟨c, rfl⟩) | ⟨c, rfl⟩) _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
  · exact commute_pinnedX_of_rootForm_eq_zero (t := TwistTag.E6) K ha he (by decide) c d
  · exact commute_pinnedX_of_rootForm_eq_zero (t := TwistTag.E6) K
      ha (IsRoot.neg he) (by decide) c d
  · exact commute_pinnedX_of_rootForm_eq_zero (t := TwistTag.E6) K hb he (by decide) c d
  · exact commute_pinnedX_of_rootForm_eq_zero (t := TwistTag.E6) K
      hb (IsRoot.neg he) (by decide) c d
  · exact commute_pinnedX_of_rootForm_eq_zero (t := TwistTag.E6) K
      (IsRoot.neg ha) he (by decide) c d
  · exact commute_pinnedX_of_rootForm_eq_zero (t := TwistTag.E6) K
      (IsRoot.neg ha) (IsRoot.neg he) (by decide) c d
  · exact commute_pinnedX_of_rootForm_eq_zero (t := TwistTag.E6) K
      (IsRoot.neg hb) he (by decide) c d
  · exact commute_pinnedX_of_rootForm_eq_zero (t := TwistTag.E6) K
      (IsRoot.neg hb) (IsRoot.neg he) (by decide) c d

theorem commute_e6C4Rho_zero_two
    (hK : ringChar K ≠ 2) (A B : SL(2, K)) : Commute (e6C4Rho K 0 A) (e6C4Rho K 2 B) := by
  obtain ⟨ha, hb, hg, hd⟩ := e6C4_roots
  have h3 := isRoot_single TwistTag.E6.tag ⟨2, by decide⟩
  have h5 := isRoot_single TwistTag.E6.tag ⟨4, by decide⟩
  have nr : ∀ {v : E6Vec}, (∀ k < cert.roots.length, cert.root k ≠ v) →
      ¬ IsRoot TwistTag.E6.tag v := fun h => not_isRoot_of_check h
  have key : ∀ g h : ModGL TwistTag.E6.tag K, g ∈ fixedGroup K → h ∈ fixedGroup K →
      ∀ ε : E6Vec, IsRoot TwistTag.E6.tag ε → rho ε = ε → ¬ Even (ε ⟨1, by decide⟩) →
      ⁅g, h⁆ ∈ rootSubgroup TwistTag.E6.tag K ε → Commute g h := by
    intro g h hg' hh ε hε hρ hodd hc
    have hmem : ⁅g, h⁆ ∈ orbitFixed K {ε} := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [Finset.coe_singleton, rootSpan_singleton]
        exact hc
      · rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem hg' hh) (inv_mem hg')) (inv_mem hh)
    rw [orbitFixed_singleton_eq_bot hK hε hρ hodd, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_commute.1 hmem
  have hA : e6C4Rho K 0 A ∈ Subgroup.closure (Set.range (fun c => e6C4Rho K 0 (tv 0 1 c)) ∪
      Set.range (fun c => e6C4Rho K 0 (tv 1 0 c))) := by
    refine range_le_of_tv _ _ (fun c => ?_) (fun c => ?_) ⟨A, rfl⟩
    · exact Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)
    · exact Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)
  have hB : e6C4Rho K 2 B ∈ Subgroup.closure (Set.range (fun c => e6C4Rho K 2 (tv 0 1 c)) ∪
      Set.range (fun c => e6C4Rho K 2 (tv 1 0 c))) := by
    refine range_le_of_tv _ _ (fun c => ?_) (fun c => ?_) ⟨B, rfl⟩
    · exact Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)
    · exact Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)
  refine commute_of_mem_closure ?_ hA hB
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩) _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
  ·
    obtain ⟨⟨t₁, t₂, hgen⟩, -⟩ := e6C4Rho_zero_gens (K := K) c
    refine key _ _ (e6C4Rho_mem_fixedGroup 0 _) (e6C4Rho_mem_fixedGroup 2 _) _ hg (by decide)
      (by decide) ?_
    dsimp only
    rw [hgen, (e6C4Rho_two_gens d).1]
    exact commutator_pinnedX_mul_mem ha hb h3 h5 hg rfl (by decide) ⟨by decide, by decide⟩
      ⟨by decide, by decide⟩ ⟨by decide, by decide, nr (by decide +kernel)⟩
      ⟨by decide, by decide, nr (by decide +kernel)⟩ ⟨by decide, by decide, nr (by decide +kernel)⟩
      ⟨by decide, by decide, nr (by decide +kernel)⟩ ⟨by decide, by decide, nr (by decide +kernel)⟩
      _ _ _ _
  ·
    obtain ⟨⟨t₁, t₂, hgen⟩, -⟩ := e6C4Rho_zero_gens (K := K) c
    refine key _ _ (e6C4Rho_mem_fixedGroup 0 _) (e6C4Rho_mem_fixedGroup 2 _) _ hd (by decide)
      (by decide) ?_
    dsimp only
    rw [hgen, (e6C4Rho_two_gens d).2,
      commute_pinnedX_of_not_isRoot ha hb (by decide) (by decide) (nr (by decide +kernel))]
    exact commutator_pinnedX_mul_mem hb ha (IsRoot.neg h3) (IsRoot.neg h5) hd (by decide)
      (by decide) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
      ⟨by decide, by decide, nr (by decide +kernel)⟩ ⟨by decide, by decide, nr (by decide +kernel)⟩
      ⟨by decide, by decide, nr (by decide +kernel)⟩ ⟨by decide, by decide, nr (by decide +kernel)⟩
      ⟨by decide, by decide, nr (by decide +kernel)⟩ _ _ _ _
  ·
    obtain ⟨-, ⟨t₁, t₂, hgen⟩⟩ := e6C4Rho_zero_gens (K := K) c
    refine key _ _ (e6C4Rho_mem_fixedGroup 0 _) (e6C4Rho_mem_fixedGroup 2 _) _ (IsRoot.neg hd)
      (by decide) (by decide) ?_
    dsimp only
    rw [hgen, (e6C4Rho_two_gens d).1, commute_pinnedX_of_not_isRoot (IsRoot.neg ha)
      (IsRoot.neg hb) (by decide) (by decide) (nr (by decide +kernel))]
    exact commutator_pinnedX_mul_mem (IsRoot.neg hb) (IsRoot.neg ha) h3 h5 (IsRoot.neg hd)
      (by decide) (by decide) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
      ⟨by decide, by decide, nr (by decide +kernel)⟩ ⟨by decide, by decide, nr (by decide +kernel)⟩
      ⟨by decide, by decide, nr (by decide +kernel)⟩ ⟨by decide, by decide, nr (by decide +kernel)⟩
      ⟨by decide, by decide, nr (by decide +kernel)⟩ _ _ _ _
  ·
    obtain ⟨-, ⟨t₁, t₂, hgen⟩⟩ := e6C4Rho_zero_gens (K := K) c
    refine key _ _ (e6C4Rho_mem_fixedGroup 0 _) (e6C4Rho_mem_fixedGroup 2 _) _ (IsRoot.neg hg)
      (by decide) (by decide) ?_
    dsimp only
    rw [hgen, (e6C4Rho_two_gens d).2]
    exact commutator_pinnedX_mul_mem (IsRoot.neg ha) (IsRoot.neg hb) (IsRoot.neg h3)
      (IsRoot.neg h5) (IsRoot.neg hg) (by decide) (by decide) ⟨by decide, by decide⟩
      ⟨by decide, by decide⟩ ⟨by decide, by decide, nr (by decide +kernel)⟩
      ⟨by decide, by decide, nr (by decide +kernel)⟩ ⟨by decide, by decide, nr (by decide +kernel)⟩
      ⟨by decide, by decide, nr (by decide +kernel)⟩ ⟨by decide, by decide, nr (by decide +kernel)⟩
      _ _ _ _

end CFSG.ComponentClassification.CatLeafProof
