module

public import CFSG.Adapters.Involutions

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup

variable {G : Type*} [Group G]

theorem mem_sylow_of_le_centralizer [Finite G] {z : G} (hz : orderOf z = 2) (S : Sylow 2 G)
    (hSM : (S : Subgroup G) ≤ centralizer ({z} : Set G)) : z ∈ (S : Subgroup G) := by
  have hZ : IsPGroup 2 (zpowers z) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hz, pow_one]
  have hnorm : (S : Subgroup G) ≤ normalizer ((zpowers z : Subgroup G) : Set G) := by
    intro s hs
    rw [mem_normalizer_iff]
    intro x
    have hsz : s * z = z * s := mem_centralizer_singleton_iff.mp (hSM hs)
    have hconj : ∀ k : ℤ, s * z ^ k * s⁻¹ = z ^ k := fun k => by
      rw [(Commute.zpow_right hsz k).eq, mul_inv_cancel_right]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, (hconj k).symm⟩
    · intro hx
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hx
      refine ⟨k, ?_⟩
      calc z ^ k = s⁻¹ * (s * z ^ k * s⁻¹) * s := by group
        _ = s⁻¹ * (s * x * s⁻¹) * s := by rw [hconj k, hk]
        _ = x := by group
  have hsup := S.is_maximal' (S.isPGroup'.to_sup_of_normal_right' hZ hnorm) le_sup_left
  rw [← hsup]
  exact mem_sup_right (mem_zpowers z)

theorem simple_two_central_involution_has_local_conjugate {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {z : G} (hz : orderOf z = 2)
    (S : Sylow 2 G) (hSM : (S : Subgroup G) ≤ centralizer ({z} : Set G)) :
    (∃ a ∈ (S : Subgroup G), a ≠ z ∧ ∃ g : G, a = g⁻¹ * z * g) ∧
    ¬ (∀ g : G, g⁻¹ * z * g ∈ (S : Subgroup G) → g⁻¹ * z * g = z) ∧
    ∀ Q : Subgroup G, Q ≤ centralizer ({z} : Set G) →
      ∀ [(Q.subgroupOf (centralizer ({z} : Set G))).Normal], z ∈ Q →
      Xor (∃ b ∈ Q, (∃ g : G, b = g⁻¹ * z * g) ∧ orderOf b = 2 ∧ b ≠ z)
        ({b | b ∈ Q ∧ ∃ g : G, b = g⁻¹ * z * g} = {z} ∧
          ∃ a, (a ∈ (S : Subgroup G) ∧ ∃ g : G, a = g⁻¹ * z * g) ∧ a ∉ Q ∧
            ∃ ha : a ∈ centralizer ({z} : Set G),
              orderOf (QuotientGroup.mk ⟨a, ha⟩ :
                centralizer ({z} : Set G) ⧸ Q.subgroupOf (centralizer ({z} : Set G))) = 2) := by
  have hzS := mem_sylow_of_le_centralizer hz S hSM
  have hzZ : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ center (S : Subgroup G) := by
    rw [mem_center_iff]
    intro s
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hSM s.2))
  have hzord : orderOf (⟨z, hzS⟩ : (S : Subgroup G)) = 2 := by rw [Subgroup.orderOf_mk, hz]
  have hnwc : ¬ ∀ g : G, g⁻¹ * z * g ∈ (S : Subgroup G) → g⁻¹ * z * g = z := by
    intro hwc
    have hcen := (CFSG.Adapters.glauberman_zStar S ⟨z, hzS⟩ hzZ hzord hwc).2
    have hodd : CFSG.oddCore G = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.oddCore G) with h | h
      · exact h
      · exact absurd (h ▸ mem_top z) (CFSG.Adapters.not_mem_oddCore_of_orderOf_eq_two hz)
    have hzc : ∀ g : G, g * z = z * g := by
      intro g
      have h := mem_center_iff.mp hcen (QuotientGroup.mk g)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hodd,
        mem_bot] at h
      exact inv_mul_eq_one.mp h
    have hcenter : center G = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
      · exact h
      · obtain ⟨a, b, hab⟩ := hnonab
        exact absurd (mem_center_iff.mp (h ▸ mem_top b) a) hab
    have hz1 : z = 1 := by
      have : z ∈ center G := mem_center_iff.mpr hzc
      rwa [hcenter, mem_bot] at this
    rw [hz1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hconj : ∃ a ∈ (S : Subgroup G), a ≠ z ∧ ∃ g : G, a = g⁻¹ * z * g := by
    by_contra hcon
    apply hnwc
    intro g hg
    by_contra hne
    exact hcon ⟨g⁻¹ * z * g, hg, hne, g, rfl⟩
  have hord : ∀ g : G, orderOf (g⁻¹ * z * g) = 2 := fun g => by
    rw [← hz]
    exact (SemiconjBy.orderOf_eq g⁻¹ (show g⁻¹ * z = g⁻¹ * z * g * g⁻¹ by group)).symm
  refine ⟨hconj, hnwc, fun Q hQM hQn hzQ => ?_⟩
  by_cases h : ∃ b ∈ Q, (∃ g : G, b = g⁻¹ * z * g) ∧ orderOf b = 2 ∧ b ≠ z
  · refine Or.inl ⟨h, fun hii => ?_⟩
    have hset := hii.1
    obtain ⟨b, hbQ, hbz, -, hbne⟩ := h
    have : b ∈ ({b | b ∈ Q ∧ ∃ g : G, b = g⁻¹ * z * g} : Set G) := ⟨hbQ, hbz⟩
    rw [hset] at this
    exact hbne this
  · refine Or.inr ⟨?_, h⟩
    have hset : {b | b ∈ Q ∧ ∃ g : G, b = g⁻¹ * z * g} = ({z} : Set G) := by
      ext b
      constructor
      · rintro ⟨hbQ, g, rfl⟩
        by_contra hne
        exact h ⟨_, hbQ, ⟨g, rfl⟩, hord g, hne⟩
      · rintro rfl
        exact ⟨hzQ, 1, by group⟩
    obtain ⟨a, haS, hane, g, rfl⟩ := hconj
    have haQ : g⁻¹ * z * g ∉ Q := fun haQ => h ⟨_, haQ, ⟨g, rfl⟩, hord g, hane⟩
    refine ⟨hset, g⁻¹ * z * g, ⟨haS, g, rfl⟩, haQ, hSM haS, ?_⟩
    have hsq : (g⁻¹ * z * g) ^ 2 = 1 := by rw [← hord g, pow_orderOf_eq_one]
    have hsq' : (⟨g⁻¹ * z * g, hSM haS⟩ : centralizer ({z} : Set G)) ^ 2 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hsq)
    refine orderOf_eq_prime ?_ ?_
    · rw [← QuotientGroup.mk_pow, hsq', QuotientGroup.mk_one]
    · intro h1
      rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
      exact haQ h1

end CFSG.LocalAnalysis.GorensteinLyons
