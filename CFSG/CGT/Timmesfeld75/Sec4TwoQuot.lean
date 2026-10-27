module

public import CFSG.CGT.Timmesfeld75.Sec4OneQuotient

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

section Img

variable {G : Type} [Group G] {K N T : Subgroup G} [hN : (N.subgroupOf K).Normal]

theorem mk_eq_one_iff_mem (x : ↥K) :
    (QuotientGroup.mk x : ↥K ⧸ N.subgroupOf K) = 1 ↔ (x : G) ∈ N :=
  (QuotientGroup.eq_one_iff x).trans Subgroup.mem_subgroupOf

theorem mk_mem_img {x : ↥K} (hx : (x : G) ∈ T) :
    (QuotientGroup.mk x : ↥K ⧸ N.subgroupOf K) ∈
      (T.subgroupOf K).map (QuotientGroup.mk' (N.subgroupOf K)) :=
  Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx)

theorem strongWC_img (hT : IsWC T) (hTK : T ≤ K)
    (hP : ∀ g ∈ K, conjSubgroup g T ≠ T → ∀ t ∈ T, t ∉ N → ∀ c ∈ conjSubgroup g T, c ∉ N →
      (c * t)⁻¹ * (t * c) ∉ N) :
    StrongWC ((T.subgroupOf K).map (QuotientGroup.mk' (N.subgroupOf K))) := by
  refine ⟨isElemAbelian_map_of_hom (isWC_subgroupOf hT K hTK).1 _, ?_⟩
  intro tb htb htb1 ab hab gb hgb
  obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.1 htb
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 hab
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective gb
  have htT : (t' : G) ∈ T := Subgroup.mem_subgroupOf.1 ht'
  have haT : (a' : G) ∈ T := Subgroup.mem_subgroupOf.1 ha'
  have htN : (t' : G) ∉ N := fun hmem => htb1 ((mk_eq_one_iff_mem t').2 hmem)
  have hc : (g' : G)⁻¹ * (a' : G) * g' ∈ conjSubgroup (g' : G)⁻¹ T := by
    rw [mem_conjSubgroup]
    have e : ((g' : G)⁻¹)⁻¹ * ((g' : G)⁻¹ * (a' : G) * g') * (g' : G)⁻¹ = a' := by group
    rw [e]
    exact haT
  change (QuotientGroup.mk (g'⁻¹ * a' * g') : ↥K ⧸ N.subgroupOf K) ∈ _
  by_cases hcT : conjSubgroup (g' : G)⁻¹ T = T
  · exact mk_mem_img (by rw [← hcT]; exact hc)
  · by_cases hcN : (g' : G)⁻¹ * (a' : G) * g' ∈ N
    · have : (QuotientGroup.mk (g'⁻¹ * a' * g') : ↥K ⧸ N.subgroupOf K) = 1 :=
        (mk_eq_one_iff_mem _).2 hcN
      rw [this]
      exact one_mem _
    · exfalso
      have hcomm := Subgroup.mem_centralizer_singleton_iff.1 hgb
      have h1 := QuotientGroup.eq.1 (hcomm : (QuotientGroup.mk (g'⁻¹ * a' * g') :
        ↥K ⧸ N.subgroupOf K) * QuotientGroup.mk t' = QuotientGroup.mk t' *
          QuotientGroup.mk (g'⁻¹ * a' * g'))
      exact hP ((g'⁻¹ : ↥K) : G) (g'⁻¹).2 hcT t' htT htN _ hc hcN
        (Subgroup.mem_subgroupOf.1 h1)

theorem img_inf_center_eq_bot (hTK : T ≤ K)
    (hP : ∀ g ∈ K, conjSubgroup g T ≠ T → ∀ t ∈ T, t ∉ N → ∀ c ∈ conjSubgroup g T, c ∉ N →
      (c * t)⁻¹ * (t * c) ∉ N)
    {g₁ : G} (hg₁ : g₁ ∈ K) (hne : conjSubgroup g₁ T ≠ T) {c₁ : G}
    (hc₁ : c₁ ∈ conjSubgroup g₁ T) (hc₁N : c₁ ∉ N) :
    (T.subgroupOf K).map (QuotientGroup.mk' (N.subgroupOf K)) ⊓
      Subgroup.center (↥K ⧸ N.subgroupOf K) = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzT, hzZ⟩
  obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.1 hzT
  rw [Subgroup.mem_bot]
  by_contra hz1
  have htT : (t' : G) ∈ T := Subgroup.mem_subgroupOf.1 ht'
  have htN : (t' : G) ∉ N := fun hmem => hz1 ((mk_eq_one_iff_mem t').2 hmem)
  have hc₁K : c₁ ∈ K := conjSubgroup_le_of_le_of_mem hTK hg₁ hc₁
  have hcomm := Subgroup.mem_center_iff.1 hzZ (QuotientGroup.mk (⟨c₁, hc₁K⟩ : ↥K))
  have h1 := QuotientGroup.eq.1 (hcomm : (QuotientGroup.mk (⟨c₁, hc₁K⟩ : ↥K) :
    ↥K ⧸ N.subgroupOf K) * QuotientGroup.mk t' = QuotientGroup.mk t' *
      QuotientGroup.mk (⟨c₁, hc₁K⟩ : ↥K))
  exact hP g₁ hg₁ hne t' htT htN c₁ hc₁ hc₁N (Subgroup.mem_subgroupOf.1 h1)

theorem card_img_mul_card_inf (hTK : T ≤ K) :
    Nat.card ((T.subgroupOf K).map (QuotientGroup.mk' (N.subgroupOf K))) *
      Nat.card (T ⊓ N : Subgroup G) = Nat.card T := by
  let φ : ↥T →* ↥K ⧸ N.subgroupOf K :=
    (QuotientGroup.mk' (N.subgroupOf K)).comp (Subgroup.inclusion hTK)
  have hrange : φ.range = (T.subgroupOf K).map (QuotientGroup.mk' (N.subgroupOf K)) := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact Subgroup.mem_map.2 ⟨Subgroup.inclusion hTK t,
        Subgroup.mem_subgroupOf.2 t.2, rfl⟩
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hz
      exact ⟨⟨(y : G), Subgroup.mem_subgroupOf.1 hy⟩, rfl⟩
  have hker : φ.ker = N.subgroupOf T := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact mk_eq_one_iff_mem (Subgroup.inclusion hTK t)
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hker, hrange] at h
  have hc : Nat.card (N.subgroupOf T) = Nat.card (T ⊓ N : Subgroup G) := by
    rw [← inf_comm, ← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : N ⊓ T ≤ T)).toEquiv
  rw [hc] at h
  rw [mul_comm]
  exact h

theorem normalClosure_img_eq_top
    (hcl : Subgroup.normalClosure ((T.subgroupOf K : Subgroup ↥K) : Set ↥K) = ⊤) :
    Subgroup.normalClosure
      (((T.subgroupOf K).map (QuotientGroup.mk' (N.subgroupOf K)) :
        Subgroup (↥K ⧸ N.subgroupOf K)) : Set (↥K ⧸ N.subgroupOf K)) = ⊤ := by
  have h := Subgroup.map_normalClosure ((T.subgroupOf K : Subgroup ↥K) : Set ↥K)
    (QuotientGroup.mk' (N.subgroupOf K)) (QuotientGroup.mk'_surjective _)
  rw [hcl, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
  rw [← Subgroup.coe_map] at h
  exact h.symm

theorem not_normal_img {g₁ : G} (hg₁ : g₁ ∈ K) {c₁ : G} (hc₁ : c₁ ∈ conjSubgroup g₁ T)
    (hTK : T ≤ K) (hc₁t : ∀ t ∈ T, t⁻¹ * c₁ ∉ N) :
    ¬ ∀ g : ↥K ⧸ N.subgroupOf K,
      conjSubgroup g ((T.subgroupOf K).map (QuotientGroup.mk' (N.subgroupOf K))) =
        (T.subgroupOf K).map (QuotientGroup.mk' (N.subgroupOf K)) := by
  intro hnorm
  have h := hnorm (QuotientGroup.mk (⟨g₁, hg₁⟩ : ↥K))
  rw [conjSubgroup_map_subgroupOf] at h
  have hc₁K : c₁ ∈ K := conjSubgroup_le_of_le_of_mem hTK hg₁ hc₁
  have hmem : (QuotientGroup.mk (⟨c₁, hc₁K⟩ : ↥K) : ↥K ⧸ N.subgroupOf K) ∈
      ((conjSubgroup ((⟨g₁, hg₁⟩ : ↥K) : G) T).subgroupOf K).map
        (QuotientGroup.mk' (N.subgroupOf K)) := mk_mem_img (T := conjSubgroup g₁ T) hc₁
  rw [h] at hmem
  obtain ⟨y, hy, hyc⟩ := Subgroup.mem_map.1 hmem
  have h1 := QuotientGroup.eq.1 hyc
  exact hc₁t (y : G) (Subgroup.mem_subgroupOf.1 hy) (Subgroup.mem_subgroupOf.1 h1)

end Img

end CFSG.CGT.Timmesfeld75
