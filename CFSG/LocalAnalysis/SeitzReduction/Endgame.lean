module

public import CFSG.GroupTheory.ThompsonIndexTwo

public section

namespace CFSG.SeitzReduction

open Subgroup

variable {G : Type*} [Group G]

theorem mem_or_mul_mem_of_mem_sup_zpowers {Y : Subgroup G} {t : G} (ht : t * t = 1)
    (htN : t ∈ normalizer (Y : Set G)) {h : G} (hh : h ∈ Y ⊔ zpowers t) :
    h ∈ Y ∨ h * t ∈ Y := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hconj : ∀ y, y ∈ Y → t * y * t ∈ Y := fun y hy => by
    have := (mem_normalizer_iff.1 htN y).1 hy
    rwa [htinv] at this
  let K : Subgroup G :=
    { carrier := {g | g ∈ Y ∨ g * t ∈ Y}
      one_mem' := Or.inl Y.one_mem
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (Y.mul_mem ha hb)
        · exact Or.inr (by simpa only [mul_assoc] using Y.mul_mem ha hb)
        · have key : a * b * t = a * t * (t * b * t) := by
            calc a * b * t = a * (t * t) * b * t := by simp only [ht, mul_one]
              _ = a * t * (t * b * t) := by group
          exact Or.inr (key ▸ Y.mul_mem ha (hconj b hb))
        · have key : a * b = a * t * (t * (b * t) * t) := by
            calc a * b = a * (t * t) * b * (t * t) := by simp only [ht, mul_one]
              _ = a * t * (t * (b * t) * t) := by group
          exact Or.inl (key ▸ Y.mul_mem ha (hconj _ hb))
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (Y.inv_mem ha)
        · have key : a⁻¹ * t = t * (a * t)⁻¹ * t := by group
          exact Or.inr (key ▸ hconj _ (Y.inv_mem ha)) }
  have hle : Y ⊔ zpowers t ≤ K :=
    sup_le (fun y hy => Or.inl hy) (zpowers_le.2 (Or.inr (by rw [ht]; exact Y.one_mem)))
  exact hle hh

theorem relIndex_inf_eq_two {Y T : Subgroup G} {t : G} (ht : t * t = 1)
    (htN : t ∈ normalizer (Y : Set G)) (htY : t ∉ Y) (hTH : T ≤ Y ⊔ zpowers t) (htT : t ∈ T) :
    (T ⊓ Y).relIndex T = 2 := by
  rw [relIndex, index_eq_two_iff]
  refine ⟨⟨t, htT⟩, fun b => ?_⟩
  simp only [mem_subgroupOf, coe_mul, mem_inf, SetLike.coe_mem, true_and]
  by_cases hb : (b : G) ∈ Y
  · refine Or.inr ⟨hb, fun hbt => htY ?_⟩
    simpa using Y.mul_mem (Y.inv_mem hb) hbt.2
  · exact Or.inl ⟨⟨T.mul_mem b.2 htT,
      (mem_or_mul_mem_of_mem_sup_zpowers ht htN (hTH b.2)).resolve_left hb⟩, hb⟩

theorem not_exists_normal_index_two_of_simple [IsSimpleGroup G] (hG : 2 < Nat.card G) :
    ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  rintro ⟨N, hN, hidx⟩
  rcases hN.eq_bot_or_eq_top with rfl | rfl
  · rw [index_bot] at hidx
    omega
  · rw [index_top] at hidx
    omega

variable [Finite G]

theorem exists_sylow_mem_le_of_not_dvd_index {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hH : ¬ p ∣ H.index) {t : G} (htH : t ∈ H) {n : ℕ} (ht : orderOf t = p ^ n) :
    ∃ T : Sylow p G, t ∈ T ∧ (T : Subgroup G) ≤ H := by
  have hp : IsPGroup p (zpowers (⟨t, htH⟩ : H)) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, ht])
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have hidx : ¬ p ∣ ((P : Subgroup H).map H.subtype).index := by
    rw [index_map_subtype]
    exact (Fact.out : p.Prime).not_dvd_mul P.not_dvd_index hH
  exact ⟨(P.isPGroup'.map H.subtype).toSylow hidx, ⟨⟨t, htH⟩, hP (mem_zpowers _), rfl⟩,
    map_subtype_le _⟩

theorem exists_normal_index_two_of_not_fused {Y : Subgroup G} {t : G} (ht : orderOf t = 2)
    (htN : t ∈ Subgroup.normalizer (Y : Set G)) (htY : t ∉ Y)
    (hsyl : ¬ 2 ∣ (Y ⊔ Subgroup.zpowers t).index) (hfus : ∀ g : G, g⁻¹ * t * g ∉ Y) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨T, htT, hTH⟩ := exists_sylow_mem_le_of_not_dvd_index hsyl
    ((le_sup_right : zpowers t ≤ Y ⊔ zpowers t) (mem_zpowers t)) (ht.trans (pow_one 2).symm)
  refine CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson T.isPGroup' T.not_dvd_index
    inf_le_left (relIndex_inf_eq_two htt htN htY hTH htT) htT (fun h => htY h.2)
    (fun y _ hyU => ?_) (fun g hg => hfus g hg.2)
  have hy : orderOf y ≠ 1 := fun h => hyU (orderOf_eq_one_iff.1 h ▸ one_mem _)
  have := orderOf_pos y
  omega

theorem exists_normal_index_two_of_not_fused_of_sylow_le {Y : Subgroup G} {t : G}
    (ht : orderOf t = 2) (htN : t ∈ Subgroup.normalizer (Y : Set G)) (htY : t ∉ Y)
    (hsyl : ∃ T : Sylow 2 G, (T : Subgroup G) ≤ Y ⊔ Subgroup.zpowers t)
    (hfus : ∀ g : G, g⁻¹ * t * g ∉ Y) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := hsyl
  exact exists_normal_index_two_of_not_fused ht htN htY
    (fun h => T.not_dvd_index (h.trans (index_dvd_of_le hT))) hfus

theorem false_of_simple_of_not_fused [IsSimpleGroup G] (hG : 2 < Nat.card G) {Y : Subgroup G}
    {t : G} (ht : orderOf t = 2) (htN : t ∈ Subgroup.normalizer (Y : Set G)) (htY : t ∉ Y)
    (hsyl : ¬ 2 ∣ (Y ⊔ Subgroup.zpowers t).index) (hfus : ∀ g : G, g⁻¹ * t * g ∉ Y) : False :=
  not_exists_normal_index_two_of_simple hG
    (exists_normal_index_two_of_not_fused ht htN htY hsyl hfus)

theorem false_of_simple_of_not_fused_of_sylow_le [IsSimpleGroup G] (hG : 2 < Nat.card G)
    {Y : Subgroup G} {t : G} (ht : orderOf t = 2) (htN : t ∈ Subgroup.normalizer (Y : Set G))
    (htY : t ∉ Y) (hsyl : ∃ T : Sylow 2 G, (T : Subgroup G) ≤ Y ⊔ Subgroup.zpowers t)
    (hfus : ∀ g : G, g⁻¹ * t * g ∉ Y) : False :=
  not_exists_normal_index_two_of_simple hG
    (exists_normal_index_two_of_not_fused_of_sylow_le ht htN htY hsyl hfus)

end CFSG.SeitzReduction
