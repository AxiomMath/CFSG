module

public import CFSG.CGT.Timmesfeld75.Sec6Four

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

theorem conj_mem_coset_inter_classD {x : G} (hx : x ∈ normD T) {t : G}
    (ht : t ∈ T) : t⁻¹ * x * t ∈ classD T ∧ ∃ s ∈ T, t⁻¹ * x * t = x * s := by
  refine ⟨classD_conj hx.1 t, x⁻¹ * t⁻¹ * x * t, ?_, by group⟩
  have hxinv : x⁻¹ ∈ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normalizer (T : Set G)).inv_mem hx.2
  have h1 : x⁻¹ * t⁻¹ * x⁻¹⁻¹ ∈ T := conj_mem_of_mem_normalizer hxinv (T.inv_mem ht)
  have e : x⁻¹ * t⁻¹ * x * t = (x⁻¹ * t⁻¹ * x⁻¹⁻¹) * t := by group
  rw [e]
  exact T.mul_mem h1 ht

theorem Sec6Ctx.eq_conj_of_mem_coset (h62 : Sec62) (h63 : Sec63) (hc : Sec6Ctx T T₁ n m) {x : G}
    (hx : x ∈ normD T) (hxT : x ∉ T) {y : G} (hy : y ∈ classD T) {t : G} (ht : t ∈ T)
    (hyt : y = x * t) : ∃ s ∈ T, y = s⁻¹ * x * s := by
  have := hc.finite
  rcases h63 G T T₁ n m hc x hx hxT with hcard | ⟨h16, -, h4⟩
  · exact h62 G T T₁ n m hc x hx hxT hcard y hy t ht hyt
  · have hTab := hc.hy.pair.wc.1
    have hx2 : x ^ 2 = 1 := by
      rw [pow_two]
      exact mul_self_eq_one_of_mem_classD hTab hx.1
    have h23 := card_commSub_mul_card_centralizer (T := T) hTab hx2 hx.2
    have hcomm : Nat.card ↥(commSub x T) = Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) := by
      rw [h4] at h23 ⊢
      rw [h16] at h23
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h23
    have hall := (card_commSub_eq_iff hTab hx2 hx.2).1 hcomm
    subst hyt
    refine hall t ht ?_
    rw [pow_two]
    exact mul_self_eq_one_of_mem_classD hTab hy

theorem Sec6Ctx.sec65 (h62 : Sec62) (h63 : Sec63) (hc : Sec6Ctx T T₁ n m) {x : G}
    (hx : x ∈ normD T) (hxT : x ∉ T) :
    {y | y ∈ classD T ∧ ∃ t ∈ T, y = x * t} = {y | ∃ t ∈ T, y = t⁻¹ * x * t} ∧
      {y | ∃ t ∈ T, y = t⁻¹ * x * t} = {y | ∃ c ∈ commSub x T, y = x * c} := by
  have hTab := hc.hy.pair.wc.1
  refine ⟨?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨hy, t, ht, hyt⟩
      obtain ⟨s, hs, hys⟩ := hc.eq_conj_of_mem_coset h62 h63 hx hxT hy ht hyt
      exact ⟨s, hs, hys⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨hD, s, hs, hst⟩ := conj_mem_coset_inter_classD hx ht
      exact ⟨hD, s, hs, hst⟩
  · have hx2 : x ^ 2 = 1 := by
      rw [pow_two]
      exact mul_self_eq_one_of_mem_classD hTab hx.1
    exact conj_orbit_eq hTab hx2 hx.2

end CFSG.CGT.Timmesfeld75
