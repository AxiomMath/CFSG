module

public import CFSG.ClassicalInvolution.AschTight.CStar

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type} [Group G] [Finite G]

theorem exists_four_generators_of_twoRankOne {C : Subgroup G}
    (hE2 : ∀ a ∈ C, ∀ b ∈ C, orderOf a = 2 → orderOf b = 2 → a * b = b * a → a = b)
    {P : Subgroup G} (hP : IsPGroup 2 P)
    (hE3 : ∃ s : Finset G, s.card ≤ 2 ∧ Subgroup.closure (s : Set G) ⊔ (P ⊓ C) = P) :
    ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = P := by
  classical
  obtain ⟨s₁, hs₁, hcl₁⟩ := hE3
  let D : Subgroup G := P ⊓ C
  have hD : IsPGroup 2 D := hP.to_inf_left
  have hrank : NoCommutingDistinctInvolutions D := by
    intro a b hab
    have h := hE2 (a.1 : G) (Subgroup.mem_inf.mp a.1.2).2 (b.1 : G) (Subgroup.mem_inf.mp b.1.2).2
      (by rw [Subgroup.orderOf_coe]; exact a.2) (by rw [Subgroup.orderOf_coe]; exact b.2)
      (congrArg Subtype.val hab)
    exact Subtype.ext (Subtype.ext h)
  obtain ⟨t, ht2, htcl⟩ := exists_two_generators_of_noCommutingDistinctInvolutions hD hrank
  have hcl₂ : Subgroup.closure ((t.image D.subtype : Finset G) : Set G) = D := by
    rw [Finset.coe_image, ← MonoidHom.map_closure, htcl, Subgroup.map_top, Subgroup.range_subtype]
  refine ⟨s₁ ∪ t.image D.subtype, ?_, ?_⟩
  · calc (s₁ ∪ t.image D.subtype).card ≤ s₁.card + (t.image D.subtype).card :=
          Finset.card_union_le _ _
      _ ≤ 2 + 2 := add_le_add hs₁ (Finset.card_image_le.trans ht2)
      _ = 4 := rfl
  · rw [Finset.coe_union, Subgroup.closure_union, hcl₂, hcl₁]

variable {p f : ℕ} [Fact p.Prime]

theorem twoSubgroupsFourGenerated_of_edgeless_star {K : Subgroup G} {z : G} (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hz : IsClassicalMember p f K z) (hC : ControlC K) (hE : DeltaEdgeless K)
    (hCSM : CommutingSylowForcesCommuting K) (hE2 : CStarTwoRankOne K)
    (hE3 : NormalizerQuotientTwoGeneratedStar K) : TwoSubgroupsFourGenerated G := by
  have hKC : K ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hz.subnormal
  have hzo : orderOf (⟨z, hz.mem⟩ : K) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hz.orderOf_eq_two
  obtain ⟨Q, hzQ⟩ := IsPGroup.exists_le_sylow (isPGroup_two_zpowers_of_orderOf_two hzo)
  have hQq := quaternion_sylow_of_isClassicalMember hp2 hq hz Q
  have hU := uniqueInvolutionNormal_of_edgeless hz.orderOf_eq_two hz.mem hKC hC hE Q hQq
  have hT : SingleMemberControl K := singleMemberControl_of_controlC hC hE
  have hzmap : z ∈ (Q : Subgroup K).map K.subtype :=
    ⟨⟨z, hz.mem⟩, hzQ (Subgroup.mem_zpowers _), rfl⟩
  have hp2g : IsPGroup 2 ((Q : Subgroup K).map K.subtype) :=
    Q.isPGroup'.of_equiv (Subgroup.equivMapOfInjective _ K.subtype K.subtype_injective)
  obtain ⟨S, hQS⟩ := hp2g.exists_le_sylow
  have hSC := le_normalizer_of_commute_imp_normalizes Q hQq hzmap hU.1 hU.2.2.2.1 hU.2.2.2.2
    S.isPGroup' hQS (fun _ h => hU.conj_eq_of_commuting hT hCSM Q h)
  refine fourGenerated_of_sylow S fun P hPS => ?_
  have hP : IsPGroup 2 P :=
    S.isPGroup'.of_injective (Subgroup.inclusion hPS) (Subgroup.inclusion_injective hPS)
  exact exists_four_generators_of_twoRankOne hE2 hP (hE3 P hP fun x hx =>
    mem_normalizer_of_mem_centralizer_of_normal hU.2.2.2.1 hU.2.2.2.2 (hSC (hPS hx)))

theorem tightControlled_of_star (hcsm : TightCSM p f) (he2 : TightE2Star p f)
    (he3 : TightE3Star p f) : TightControlled p f := by
  intro G _ _ _ K z ht
  exact absurd (twoSubgroupsFourGenerated_of_edgeless_star ht.branch.odd ht.branch.five
    ht.branch.member ht.control ht.edgeless (hcsm G K z ht) (he2 G K z ht) (he3 G K z ht))
    ht.branch.notFourGenerated

end CFSG.ClassicalInvolution.Disconnected.AschTight
