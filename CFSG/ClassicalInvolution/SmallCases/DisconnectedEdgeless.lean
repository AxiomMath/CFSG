module

public import CFSG.ClassicalInvolution.SmallCases.DisconnectedTorus
public import CFSG.ClassicalInvolution.SmallCases.DisconnectedQuaternion

public section

namespace CFSG.ClassicalInvolution.Disconnected

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G]

@[expose] def DeltaEdgeless (K : Subgroup G) : Prop := ∀ X Y, ¬ commutingAdj K X Y

omit [Finite G] in
theorem centralizer_le_normalizer_of_edgeless {K : Subgroup G} {z : G} (hz : orderOf z = 2)
    (hKC : K ≤ Subgroup.centralizer ({z} : Set G)) (hC : ControlC K) (hE : DeltaEdgeless K) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  intro c hc
  rw [← conjSubgroup_eq_self_iff]
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hz
  have hzc : Commute z c := (Subgroup.mem_centralizer_singleton_iff.mp hc).symm
  have hKc : conjSubgroup c K ≤ Subgroup.centralizer ({z} : Set G) := by
    intro x hx
    have hk : c⁻¹ * x * c ∈ K := mem_conjSubgroup_iff.mp hx
    have hzk : Commute z (c⁻¹ * x * c) :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)).symm
    have hzx : Commute z (c * (c⁻¹ * x * c) * c⁻¹) :=
      (hzc.mul_right hzk).mul_right hzc.inv_right
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx' : c * (c⁻¹ * x * c) * c⁻¹ = x := by group
    rw [hx'] at hzx
    exact hzx.symm
  exact eq_of_mem_deltaComp_of_edgeless hE
    (hC z hz1 (isPGroup_two_zpowers_of_orderOf_two hz) K (self_mem_conjugateSet K)
      (conjSubgroup c K) (conjSubgroup_mem_conjugateSet c (self_mem_conjugateSet K)) hKC hKc)

theorem uniqueInvolutionNormal_of_edgeless {K : Subgroup G} {z : G} (hz : orderOf z = 2)
    (hzK : z ∈ K) (hKC : K ≤ Subgroup.centralizer ({z} : Set G)) (hC : ControlC K)
    (hE : DeltaEdgeless K) (T : Sylow 2 K)
    (hT : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((T : Subgroup K) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    UniqueInvolutionNormal K z :=
  uniqueInvolutionNormal_of_quaternion_sylow hz hzK hKC
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mpr
      (centralizer_le_normalizer_of_edgeless hz hKC hC hE)) T hT

variable {p f : ℕ} [Fact p.Prime]

theorem twoSubgroupsFourGenerated_of_edgeless {K : Subgroup G} {z : G} (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hz : IsClassicalMember p f K z) (hC : ControlC K) (hE : DeltaEdgeless K)
    (hCSM : CommutingSylowForcesCommuting K) (hE2 : CentralizerTwoRankOne K)
    (hE3 : NormalizerQuotientTwoGenerated K) : TwoSubgroupsFourGenerated G := by
  have hKC : K ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hz.subnormal
  have hzo : orderOf (⟨z, hz.mem⟩ : K) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hz.orderOf_eq_two
  obtain ⟨Q, hzQ⟩ := IsPGroup.exists_le_sylow
    (isPGroup_two_zpowers_of_orderOf_two hzo)
  have hQq := quaternion_sylow_of_isClassicalMember hp2 hq hz Q
  have hU := uniqueInvolutionNormal_of_edgeless hz.orderOf_eq_two hz.mem hKC hC hE Q hQq
  have hT : SingleMemberControl K := singleMemberControl_of_controlC hC hE
  have hzmap : z ∈ (Q : Subgroup K).map K.subtype :=
    ⟨⟨z, hz.mem⟩, hzQ (Subgroup.mem_zpowers _), rfl⟩
  have hp2g : IsPGroup 2 ((Q : Subgroup K).map K.subtype) :=
    Q.isPGroup'.of_equiv (Subgroup.equivMapOfInjective _ K.subtype K.subtype_injective)
  obtain ⟨S, hQS⟩ := hp2g.exists_le_sylow
  exact twoSubgroupsFourGenerated_of_tight_csm hU hT hCSM Q hQq hzmap S hQS hE2 hE3

end CFSG.ClassicalInvolution.Disconnected
