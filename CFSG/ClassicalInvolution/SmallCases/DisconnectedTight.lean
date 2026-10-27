module

public import CFSG.ClassicalInvolution.SmallCases.Rank3NormalEight
public import CFSG.ClassicalInvolution.SmallCases.DisconnectedStatements
public import CFSG.ClassicalInvolution.TwoGroupCase.Packets
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open CFSG.DisconnectedInvolutionGraph.Helpers

section TwoGenerators

theorem closure_quaternion_generators (n : ℕ) [NeZero n] :
    Subgroup.closure ({QuaternionGroup.a 1, QuaternionGroup.xa 0} :
      Set (QuaternionGroup n)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have ha : ∀ i : ZMod (2 * n), (QuaternionGroup.a i : QuaternionGroup n) ∈
      Subgroup.closure ({QuaternionGroup.a 1, QuaternionGroup.xa 0} :
        Set (QuaternionGroup n)) := by
    intro i
    have h : (QuaternionGroup.a i : QuaternionGroup n) = (QuaternionGroup.a 1) ^ i.val := by
      rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
    rw [h]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _
  cases x with
  | a i => exact ha i
  | xa i =>
    have h : (QuaternionGroup.xa i : QuaternionGroup n) =
        QuaternionGroup.xa 0 * QuaternionGroup.a i := by
      rw [QuaternionGroup.xa_mul_a, zero_add]
    rw [h]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (ha i)

theorem exists_two_generators_of_noCommutingDistinctInvolutions {H : Type*} [Group H] [Finite H]
    (hp : IsPGroup 2 H) (hr : NoCommutingDistinctInvolutions H) :
    ∃ s : Finset H, s.card ≤ 2 ∧ Subgroup.closure (s : Set H) = ⊤ := by
  classical
  rcases rank_one_two_cyclic_or_quaternion hp hr with hc | ⟨e, -, ⟨φ⟩⟩
  · obtain ⟨g, hg⟩ := hc.exists_generator
    refine ⟨{g}, by simp, ?_⟩
    rw [eq_top_iff]
    intro x _
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    simpa using Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) k
  · have : NeZero (2 ^ e) := ⟨pow_ne_zero _ two_ne_zero⟩
    refine ⟨{φ (QuaternionGroup.a 1), φ (QuaternionGroup.xa 0)}, Finset.card_le_two, ?_⟩
    have hmap := congrArg (Subgroup.map φ.toMonoidHom) (closure_quaternion_generators (2 ^ e))
    rw [MonoidHom.map_closure, Subgroup.map_top] at hmap
    have hr : φ.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr φ.surjective
    rw [hr] at hmap
    rw [← hmap]
    congr 1
    ext x
    simp [Set.image_insert_eq]

end TwoGenerators

section Count

variable {G : Type*} [Group G] [Finite G]

theorem exists_four_generators_of_le_normalizer {K : Subgroup G}
    (hE2 : CentralizerTwoRankOne K) (hE3 : NormalizerQuotientTwoGenerated K) {P : Subgroup G}
    (hP : IsPGroup 2 P) (hPN : P ≤ Subgroup.normalizer (K : Set G)) :
    ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = P := by
  classical
  obtain ⟨s₁, hs₁, hcl₁⟩ := hE3 P hP hPN
  let D : Subgroup G := P ⊓ Subgroup.centralizer (K : Set G)
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

end Count


section Tight

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem mem_normalizer_of_mem_centralizer {K : Subgroup G} {z : G}
    (hKC : K ≤ Subgroup.centralizer ({z} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal) {s : G}
    (hs : s ∈ Subgroup.centralizer ({z} : Set G)) : s ∈ Subgroup.normalizer (K : Set G) := by
  have key : ∀ t ∈ Subgroup.centralizer ({z} : Set G), ∀ k ∈ K, t * k * t⁻¹ ∈ K := by
    intro t ht k hk
    have h := hKn.conj_mem ⟨k, hKC hk⟩ (Subgroup.mem_subgroupOf.mpr hk) ⟨t, ht⟩
    exact Subgroup.mem_subgroupOf.mp h
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · exact key s hs k
  · intro hk
    have := key s⁻¹ (inv_mem hs) _ hk
    simpa [mul_assoc] using this

theorem normalizes_of_commute_imp_normalizes {K : Subgroup G} (Q : Sylow 2 K)
    (hQ : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((Q : Subgroup K) ≃* QuaternionGroup (2 ^ (r - 2))))
    {z : G} (hz : z ∈ (Q : Subgroup K).map K.subtype) (hzo : orderOf z = 2)
    (hKC : K ≤ Subgroup.centralizer ({z} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal)
    {S : Subgroup G} (hS : IsPGroup 2 S) (hQS : (Q : Subgroup K).map K.subtype ≤ S)
    (hcomm : ∀ g : G, (∀ x ∈ conjSubgroup g ((Q : Subgroup K).map K.subtype),
        ∀ y ∈ (Q : Subgroup K).map K.subtype, x * y = y * x) → conjSubgroup g K = K) :
    ∀ s ∈ S, conjSubgroup s ((Q : Subgroup K).map K.subtype) =
      (Q : Subgroup K).map K.subtype := by
  intro s hs
  by_contra hne
  have h1 : conjSubgroup 1 ((Q : Subgroup K).map K.subtype) ≤ S := by
    rw [conjSubgroup_one]
    exact hQS
  have h2 : conjSubgroup s ((Q : Subgroup K).map K.subtype) ≤ S := by
    intro x hx
    have hx' := hQS (mem_conjSubgroup_iff.mp hx)
    have e : x = s * (s⁻¹ * x * s) * s⁻¹ := by group
    rw [e]
    exact S.mul_mem (S.mul_mem hs hx') (S.inv_mem hs)
  have hne' : conjSubgroup 1 ((Q : Subgroup K).map K.subtype) ≠
      conjSubgroup s ((Q : Subgroup K).map K.subtype) := by
    rw [conjSubgroup_one]
    exact fun h => hne h.symm
  obtain ⟨-, hcommute⟩ := quaternion_conjugates_commute Q hQ hz hzo hKC hKn hS hQS h1 h2 hne'
  have hK : conjSubgroup s K = K := by
    refine hcomm s fun x hx y hy => ?_
    exact (hcommute y (by rwa [conjSubgroup_one]) x hx).symm
  have hle : conjSubgroup s ((Q : Subgroup K).map K.subtype) ≤
      (Q : Subgroup K).map K.subtype := by
    intro x hx
    have hxK : x ∈ K := by
      have : conjSubgroup s ((Q : Subgroup K).map K.subtype) ≤ conjSubgroup s K :=
        conjSubgroup_mono (Subgroup.map_subtype_le _)
      rw [hK] at this
      exact this hx
    have hxS : x ∈ S := h2 hx
    have hSK : IsPGroup 2 (S.subgroupOf K) := hS.comap_subtype
    have hQle : (Q : Subgroup K) ≤ S.subgroupOf K := by
      intro q hq
      exact hQS ⟨q, hq, rfl⟩
    have heq : S.subgroupOf K = (Q : Subgroup K) := Q.is_maximal' hSK hQle
    have hmem : (⟨x, hxK⟩ : K) ∈ S.subgroupOf K := Subgroup.mem_subgroupOf.mpr hxS
    rw [heq] at hmem
    exact ⟨⟨x, hxK⟩, hmem, rfl⟩
  have hcard : Nat.card ((Q : Subgroup K).map K.subtype) ≤
      Nat.card (conjSubgroup s ((Q : Subgroup K).map K.subtype)) := by
    rw [card_conjSubgroup]
  exact hne (Subgroup.eq_of_le_of_card_ge hle hcard)


theorem le_normalizer_of_commute_imp_normalizes {K : Subgroup G} (Q : Sylow 2 K)
    (hQ : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((Q : Subgroup K) ≃* QuaternionGroup (2 ^ (r - 2))))
    {z : G} (hz : z ∈ (Q : Subgroup K).map K.subtype) (hzo : orderOf z = 2)
    (hKC : K ≤ Subgroup.centralizer ({z} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal)
    {S : Subgroup G} (hS : IsPGroup 2 S) (hQS : (Q : Subgroup K).map K.subtype ≤ S)
    (hcomm : ∀ g : G, (∀ x ∈ conjSubgroup g ((Q : Subgroup K).map K.subtype),
        ∀ y ∈ (Q : Subgroup K).map K.subtype, x * y = y * x) → conjSubgroup g K = K) :
    S ≤ Subgroup.centralizer ({z} : Set G) := by
  intro s hs
  have hQn := normalizes_of_commute_imp_normalizes Q hQ hz hzo hKC hKn hS hQS hcomm s hs
  have hzK : z ∈ K := (Subgroup.map_subtype_le _) hz
  have hmem : s * z * s⁻¹ ∈ conjSubgroup s ((Q : Subgroup K).map K.subtype) :=
    mem_conjSubgroup_of_mem hz
  rw [hQn] at hmem
  have hsz : s * z * s⁻¹ ∈ K := (Subgroup.map_subtype_le _) hmem
  have hord : orderOf (s * z * s⁻¹) = 2 := by
    have := (MulAut.conj s).orderOf_eq z
    simpa [MulAut.conj_apply, hzo] using this
  obtain ⟨hU, -⟩ := unique_involution_of_quaternion_sylow hzK hzo hKC Q hQ
  have heq : s * z * s⁻¹ = z := hU _ hsz hord
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc s * z = (s * z * s⁻¹) * s := by group
    _ = z * s := by rw [heq]

end Tight

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem twoSubgroupsFourGenerated_of_tight_quaternion {K : Subgroup G} (Q : Sylow 2 K)
    (hQ : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((Q : Subgroup K) ≃* QuaternionGroup (2 ^ (r - 2))))
    {z : G} (hz : z ∈ (Q : Subgroup K).map K.subtype) (hzo : orderOf z = 2)
    (hKC : K ≤ Subgroup.centralizer ({z} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal)
    (S : Sylow 2 G) (hQS : (Q : Subgroup K).map K.subtype ≤ S)
    (hcomm : ∀ g : G, (∀ x ∈ conjSubgroup g ((Q : Subgroup K).map K.subtype),
        ∀ y ∈ (Q : Subgroup K).map K.subtype, x * y = y * x) → conjSubgroup g K = K)
    (hE2 : CentralizerTwoRankOne K) (hE3 : NormalizerQuotientTwoGenerated K) :
    TwoSubgroupsFourGenerated G := by
  have hSC := le_normalizer_of_commute_imp_normalizes Q hQ hz hzo hKC hKn S.isPGroup' hQS hcomm
  refine fourGenerated_of_sylow S fun P hPS => ?_
  have hP : IsPGroup 2 P :=
    S.isPGroup'.of_injective (Subgroup.inclusion hPS) (Subgroup.inclusion_injective hPS)
  exact exists_four_generators_of_le_normalizer hE2 hE3 hP fun p hp =>
    mem_normalizer_of_mem_centralizer hKC hKn (hSC (hPS hp))

end Assembly

end CFSG.ClassicalInvolution
