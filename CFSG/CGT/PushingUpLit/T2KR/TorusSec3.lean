module

public import CFSG.CGT.PushingUpLit.T2KR.TorusPair
public import CFSG.CGT.Timmesfeld75.Sec3OddSubgroup

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped MatrixGroups

section Quotient

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}
  [hN : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal]

set_option quotPrecheck false in
local notation "XQ" => ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)

set_option quotPrecheck false in
local notation "TQ" =>
  (T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))

set_option quotPrecheck false in
local notation "T₁Q" =>
  (T₁.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))

omit [Finite G] in
theorem exists_eq_mul_cfgM_of_map_mem_right {y : G} (hy : y ∈ T ⊔ T₁)
    (h : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨y, hy⟩ ∈ T₁Q) :
    ∃ t ∈ T₁, ∃ m ∈ cfgM T T₁, y = t * m := by
  obtain ⟨z, hz, hzy⟩ := h
  have h1 : (z : G)⁻¹ * y ∈ cfgM T T₁ := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hzy)
  exact ⟨z, Subgroup.mem_subgroupOf.1 hz, _, h1, by group⟩

omit [Finite G] in
theorem map_mem_conjSubgroup_map_right {t y : G} (ht : t ∈ T ⊔ T₁) (hy : y ∈ T ⊔ T₁)
    (hyt : y ∈ conjSubgroup t T₁) :
    QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨y, hy⟩ ∈
      conjSubgroup (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨t, ht⟩) T₁Q := by
  rw [← map_conjSubgroup, conjSubgroup_subgroupOf]
  exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hyt)

omit [Finite G] in
theorem conjSubgroup_map_eq_right {x₀ : G} (hx₀ : x₀ ∈ T ⊔ T₁) (h : T₁ = conjSubgroup x₀ T) :
    conjSubgroup (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨x₀, hx₀⟩) TQ = T₁Q := by
  rw [← map_conjSubgroup, conjSubgroup_subgroupOf, ← h]

theorem Sec3.exists_odd_normalizing_pair (hS : Sec3 T T₁) (hS' : Sec3 T₁ T) {f : ℕ}
    (hf : 2 ≤ f)
    (h : Nonempty (XQ ≃* PSL(2, GaloisField 2 f))) :
    ∃ k ∈ T ⊔ T₁, k ∈ Subgroup.normalizer (T : Set G) ∧ k ∈ Subgroup.normalizer (T₁ : Set G) ∧
      k ≠ 1 ∧ ∀ m ∈ cfgM T T₁, k * m * k⁻¹ = m → m = 1 := by
  have hf0 : f ≠ 0 := by omega
  have hX := hS.isL2Pair_quotient hf0 h
  obtain ⟨x₀, hx₀X, hx₀⟩ := hS.conj
  have hconj := conjSubgroup_map_eq_right hx₀X hx₀
  have hne : conjSubgroup (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨x₀, hx₀X⟩) TQ ≠
      TQ := by
    rw [hconj]
    exact hS.map_ne_map
  obtain ⟨H, hHT, hHT₁, hHcard⟩ := l2Pair_exists_twoPoint_torus hX hne
  rw [hconj] at hHT₁
  have hodd : Odd (Nat.card H) := by
    rw [hHcard]
    exact osg_odd_two_pow_sub_one hf0
  have hM2 : IsPGroup 2 ((cfgM T T₁).subgroupOf (T ⊔ T₁)) :=
    (isPGroup_two_of_isElemAbelian hS.cfg.isElemAbelian_cfgM).comap_subtype
  obtain ⟨K₀, hK₀card, hK₀H, hK₀1⟩ :=
    osg_exists_lift ((cfgM T T₁).subgroupOf (T ⊔ T₁)) hM2 H hodd
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hK₀gt : 1 < Nat.card K₀ := by
    rw [hK₀card, hHcard]
    omega
  obtain ⟨k, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    ((Subgroup.one_lt_card_iff_ne_bot K₀).1 hK₀gt)
  have hk : (k : ↥(T ⊔ T₁)) ∈ K₀ := k.2
  have hk1' : (k : ↥(T ⊔ T₁)) ≠ 1 := fun h' => hk1 (Subtype.ext h')
  have hkX : ((k : ↥(T ⊔ T₁)) : G) ∈ T ⊔ T₁ := (k : ↥(T ⊔ T₁)).2
  have hπk := hK₀H _ hk
  refine ⟨((k : ↥(T ⊔ T₁)) : G), hkX, ?_, ?_, ?_, ?_⟩
  · refine mem_normalizer_of_conjSubgroup_eq
      (hS.conjSubgroup_eq_of_le_mul_cfgM hkX fun z hz => ?_)
    have hzX : z ∈ T ⊔ T₁ := conjSubgroup_le_of_le_of_mem le_sup_left hkX hz
    refine osg_exists_eq_mul_cfgM_of_map_mem_left hzX ?_
    have h1 := map_mem_conjSubgroup_map hkX hzX hz
    have h2 : conjSubgroup
        (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨((k : ↥(T ⊔ T₁)) : G), hkX⟩)
        TQ = TQ := mem_normalizer_iff_conjSubgroup_eq.1 (hHT hπk)
    rwa [h2] at h1
  · have hkX' : ((k : ↥(T ⊔ T₁)) : G) ∈ T₁ ⊔ T := by rw [sup_comm]; exact hkX
    refine mem_normalizer_of_conjSubgroup_eq
      (hS'.conjSubgroup_eq_of_le_mul_cfgM hkX' fun z hz => ?_)
    have hzX' : z ∈ T₁ ⊔ T := conjSubgroup_le_of_le_of_mem le_sup_left hkX' hz
    have hzX : z ∈ T ⊔ T₁ := by rw [sup_comm]; exact hzX'
    have hzc : z ∈ conjSubgroup ((k : ↥(T ⊔ T₁)) : G) T₁ := hz
    have h1 := map_mem_conjSubgroup_map_right hkX hzX hzc
    have h2 : conjSubgroup
        (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨((k : ↥(T ⊔ T₁)) : G), hkX⟩)
        T₁Q = T₁Q := mem_normalizer_iff_conjSubgroup_eq.1 (hHT₁ hπk)
    rw [h2] at h1
    obtain ⟨t, ht, m, hm, rfl⟩ := exists_eq_mul_cfgM_of_map_mem_right hzX h1
    exact ⟨t, ht, m, by rw [cfgM_symm]; exact hm, rfl⟩
  · exact fun h1 => hk1' (Subtype.ext h1)
  · have hπ1 : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))
        ⟨((k : ↥(T ⊔ T₁)) : G), hkX⟩ ≠ 1 := fun h' => hk1' (hK₀1 _ hk h')
    have hodd' : Odd (orderOf (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))
        ⟨((k : ↥(T ⊔ T₁)) : G), hkX⟩)) := by
      have hdvd : orderOf (⟨_, hπk⟩ : H) ∣ Nat.card H := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at hdvd
      exact Odd.of_dvd_nat hodd hdvd
    exact hS.centralizer_cfgM_eq_bot_of_odd hX hkX hodd' hπ1

end Quotient

end CFSG.CGT.PushingUpLit.T2KR
