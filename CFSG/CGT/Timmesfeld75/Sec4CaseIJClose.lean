module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIJBasic
public import CFSG.CGT.Timmesfeld75.Sec4Three

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

section Gen

variable {G : Type} [Group G] {R T T₁ T₂ : Subgroup G}

theorem range_comp_inclusion_eq_sup {K : Type*} [Group K] (π : ↥R →* K) {Y : Subgroup G}
    (hY : Y = T ⊔ T₁ ⊔ T₂) (hYR : Y ≤ R) {y₁ y₂ : G} (hy₁ : y₁ ∈ R) (hy₂ : y₂ ∈ R)
    (h₁ : T₁ = conjSubgroup y₁ T) (h₂ : T₂ = conjSubgroup y₂ T) :
    (π.comp (Subgroup.inclusion hYR)).range = (T.subgroupOf R).map π ⊔
      conjSubgroup (π ⟨y₁, hy₁⟩) ((T.subgroupOf R).map π) ⊔
      conjSubgroup (π ⟨y₂, hy₂⟩) ((T.subgroupOf R).map π) := by
  subst hY
  have hTR : T ≤ R := le_sup_left.trans (le_sup_left.trans hYR)
  have hT₁R : T₁ ≤ R := le_sup_right.trans (le_sup_left.trans hYR)
  have hT₂R : T₂ ≤ R := le_sup_right.trans hYR
  rw [← MonoidHom.map_range, Subgroup.inclusion_range,
    Subgroup.subgroupOf_sup (sup_le hTR hT₁R) hT₂R, Subgroup.subgroupOf_sup hTR hT₁R,
    Subgroup.map_sup, Subgroup.map_sup]
  subst h₁ h₂
  rw [← map_conjSubgroup, ← map_conjSubgroup, conjSubgroup_subgroupOf, conjSubgroup_subgroupOf]

theorem sec4N_normalizer_of_normalizes {w : G} (hT : w ∈ Subgroup.normalizer (T : Set G))
    (hT₁ : w ∈ Subgroup.normalizer (T₁ : Set G)) (hT₂ : w ∈ Subgroup.normalizer (T₂ : Set G)) :
    w ∈ Subgroup.normalizer (sec4N T T₁ T₂ : Set G) := by
  refine mem_normalizer_of_conjSubgroup_eq ?_
  unfold sec4N
  rw [conjSubgroup_sup_eq_sup, conjSubgroup_sup_eq_sup,
    conjSubgroup_normIn_eq_of_mem_normalizer hT hT₁,
    conjSubgroup_normIn_eq_of_mem_normalizer hT₁ hT,
    conjSubgroup_normIn_eq_of_mem_normalizer hT₂ hT]

end Gen

section Four

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

theorem conjSubgroup_le_sec4Y_of_mem_normalizer
    (hAsc : AschbacherNoPolarInput)
    (h : Sec4Hyp T T₁ a T₂) (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) {c : G}
    (hc : c ∈ Subgroup.normalizer (sec4N T T₁ T₂ : Set G)) :
    conjSubgroup c T ≤ sec4Y T T₁ T₂ := by
  have hn := h.sec4_three hAsc hq
  rintro _ ⟨t, ht, rfl⟩
  have htN : t ∈ Subgroup.normalizer (sec4N T T₁ T₂ : Set G) :=
    h.sec4Y_le_normalizer (left_le_sec4Y ht)
  have := hn.conj_mem ⟨t, htN⟩ (Subgroup.mem_subgroupOf.2 (left_le_sec4Y ht)) ⟨c, hc⟩
  exact Subgroup.mem_subgroupOf.1 this

end Four

end CFSG.CGT.Timmesfeld75
