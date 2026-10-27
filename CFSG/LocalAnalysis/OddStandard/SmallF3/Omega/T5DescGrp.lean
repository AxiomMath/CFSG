module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Center

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

section Defs

variable {G : Type} [Group G]

@[expose] def DescZ (L : Subgroup G) (t : G) : Subgroup ↥(normalizer (L : Set G)) :=
  Subgroup.normalClosure {n : ↥(normalizer (L : Set G)) | (n : G) = t}

instance (L : Subgroup G) (t : G) : (DescZ L t).Normal := Subgroup.normalClosure_normal

abbrev DescG (L : Subgroup G) (t : G) : Type := ↥(normalizer (L : Set G)) ⧸ DescZ L t

@[expose] def descMk (L : Subgroup G) (t : G) : ↥(normalizer (L : Set G)) →* DescG L t :=
  QuotientGroup.mk' (DescZ L t)

@[expose] def DescL (L : Subgroup G) (t : G) : Subgroup (DescG L t) :=
  (L.subgroupOf (normalizer (L : Set G))).map (descMk L t)

@[expose] def descElt (L : Subgroup G) (t : G) (s : G) (hs : s ∈ normalizer (L : Set G)) :
    DescG L t :=
  descMk L t ⟨s, hs⟩

@[expose] def descRes (L : Subgroup G) (t : G) : ↥L →* ↥(DescL L t) :=
  ((descMk L t).subgroupMap (L.subgroupOf (normalizer (L : Set G)))).comp
    (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := L))).symm.toMonoidHom

theorem coe_descRes (L : Subgroup G) (t : G) (l : ↥L) :
    ((descRes L t l : ↥(DescL L t)) : DescG L t) =
      descMk L t ⟨(l : G), Subgroup.le_normalizer l.2⟩ := by
  rfl

theorem descRes_surjective (L : Subgroup G) (t : G) : Function.Surjective (descRes L t) := by
  intro x
  obtain ⟨y, hy⟩ :=
    MonoidHom.subgroupMap_surjective (descMk L t) (L.subgroupOf (normalizer (L : Set G))) x
  refine ⟨(Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := L))) y, ?_⟩
  show ((descMk L t).subgroupMap (L.subgroupOf (normalizer (L : Set G))))
    ((Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := L))).symm.toMonoidHom
      ((Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := L))) y)) = x
  have hsymm : (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := L))).symm.toMonoidHom
      ((Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := L))) y) = y := by
    simp
  rw [hsymm]
  exact hy

end Defs

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem descMk_eq_one_iff (hL : IsOm6Z2 L) {t : G} (ht : t ∈ centerIn L) (ht2 : orderOf t = 2)
    (n : ↥(normalizer (L : Set G))) : descMk L t n = 1 ↔ (n : G) = 1 ∨ (n : G) = t := by
  have htL : t ∈ L := Subgroup.map_subtype_le (Subgroup.center ↥L) ht
  let tN : ↥(normalizer (L : Set G)) := ⟨t, Subgroup.le_normalizer (H := L) htL⟩
  have htN_coe : (tN : G) = t := rfl
  have htN_center : tN ∈ Subgroup.center ↥(normalizer (L : Set G)) := by
    rw [Subgroup.mem_center_iff]
    intro m
    exact Subtype.ext (t5_normalizer_commute hL ht ht2 m.2)
  have htN_ord : orderOf tN = 2 := by
    have h : orderOf (tN : G) = orderOf tN :=
      orderOf_injective (Subgroup.subtype (normalizer (L : Set G)))
        (Subgroup.subtype_injective _) tN
    rw [htN_coe, ht2] at h
    exact h.symm
  have hset : {m : ↥(normalizer (L : Set G)) | (m : G) = t} = {tN} := by
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]⟩
  have hzp : DescZ L t = zpowers tN := by
    rw [DescZ, hset]
    haveI : (zpowers tN).Normal := Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr htN_center)
    refine le_antisymm (Subgroup.normalClosure_le_normal ?_) ?_
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact Subgroup.mem_zpowers tN
    · rw [Subgroup.zpowers_eq_closure]
      exact Subgroup.closure_le_normalClosure
  have hmem : n ∈ zpowers tN ↔ n = 1 ∨ n = tN := by
    rw [Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, rfl⟩
      rw [← zpow_mod_orderOf tN k, htN_ord]
      have h2 : k % (↑(2 : ℕ) : ℤ) = k % 2 := by norm_num
      rw [h2]
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · rw [h]; simp
      · rw [h]; simp
    · rintro (rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
  rw [descMk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hzp, hmem]
  constructor
  · rintro (h | h)
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · rintro (h | h)
    · exact Or.inl (Subtype.ext (by simpa using h))
    · exact Or.inr (Subtype.ext (by simpa [htN_coe] using h))

theorem descRes_eq_one_iff (hL : IsOm6Z2 L) {t : G} (ht : t ∈ centerIn L) (ht2 : orderOf t = 2)
    (l : ↥L) : descRes L t l = 1 ↔ (l : G) = 1 ∨ (l : G) = t := by
  have hiff : descRes L t l = 1 ↔ ((descRes L t l : ↥(DescL L t)) : DescG L t) = 1 := by
    rw [Subtype.ext_iff, Subgroup.coe_one]
  rw [hiff, coe_descRes, descMk_eq_one_iff hL ht ht2]

theorem descRes_ker_le_center (hL : IsOm6Z2 L) {t : G} (ht : t ∈ centerIn L)
    (ht2 : orderOf t = 2) : (descRes L t).ker ≤ Subgroup.center ↥L := by
  intro l hl
  rw [MonoidHom.mem_ker] at hl
  have h := (descRes_eq_one_iff hL ht ht2 l).mp hl
  obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp ht
  rw [Subgroup.mem_center_iff]
  intro m
  rcases h with h | h
  · have hl1 : l = 1 := Subtype.ext h
    rw [hl1, mul_one, one_mul]
  · have hla : l = a := Subtype.ext (h.trans haeq.symm)
    rw [hla]
    exact Subgroup.mem_center_iff.mp ha m

theorem descRes_center (hL : IsOm6Z2 L) {t : G} (ht : t ∈ centerIn L) (ht2 : orderOf t = 2)
    (l : ↥L) : descRes L t l ∈ Subgroup.center ↥(DescL L t) → l ∈ Subgroup.center ↥L := by
  intro hl
  have hcomm : (l : G) ∈ centralizer (L : Set G) := by
    apply t5_centralizes_of_central_comm hL.1 (Z := zpowers t) (Subgroup.zpowers_le.mpr ht)
      (Subgroup.le_normalizer (H := L) l.2)
    intro l₁ hl₁
    let l₁' : ↥L := ⟨l₁, hl₁⟩
    have hk : descRes L t (l * l₁' * l⁻¹ * l₁'⁻¹) = 1 := by
      have hc : descRes L t l₁' * descRes L t l = descRes L t l * descRes L t l₁' :=
        Subgroup.mem_center_iff.mp hl (descRes L t l₁')
      calc descRes L t (l * l₁' * l⁻¹ * l₁'⁻¹)
          = descRes L t l * descRes L t l₁' * (descRes L t l)⁻¹ *
              (descRes L t l₁')⁻¹ := by simp only [map_mul, map_inv]
        _ = descRes L t l₁' * descRes L t l * (descRes L t l)⁻¹ *
              (descRes L t l₁')⁻¹ := by rw [hc.symm]
        _ = 1 := by group
    have hk' := (descRes_eq_one_iff hL ht ht2 (l * l₁' * l⁻¹ * l₁'⁻¹)).mp hk
    have hcoe : ((l * l₁' * l⁻¹ * l₁'⁻¹ : ↥L) : G) =
        (l : G) * l₁ * (l : G)⁻¹ * l₁⁻¹ := by
      simp [l₁']
    rw [← hcoe]
    rcases hk' with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers t
  have hlc := Subgroup.mem_centralizer_iff.mp hcomm
  rw [Subgroup.mem_center_iff]
  intro m
  exact Subtype.ext (hlc (m : G) m.2)

end CFSG.OddStandard.SmallF3.Omega
