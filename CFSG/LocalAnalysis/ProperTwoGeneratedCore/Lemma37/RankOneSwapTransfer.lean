module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneSwapRoot
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneRooting

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

namespace RankOneSetting

variable (h : RankOneSetting G S H z J) {s : EscapingQuotient z}
  (hsS : s ∈ escapingSylowImage S z)
  (hs : s ∉ Subgroup.normalizer (J : Set (EscapingQuotient z)))
  (hle : ∀ t ∈ escapingSylowImage S z, t ∈ Subgroup.normalizer (J : Set (EscapingQuotient z)) →
    t ∈ J ⊔ swapComponent J s)
include h hsS hs hle

theorem sq_eq_of_mem_normalizer_swap
    {t : EscapingQuotient z} (htS : t ∈ escapingSylowImage S z)
    (htN : t ∈ Subgroup.normalizer (J : Set (EscapingQuotient z))) :
    t ^ 2 = 1 ∨ t ^ 2 = escapingBar z := by
  obtain ⟨c, hcS, hcJ, c', hc'S, hc'J', rfl⟩ :=
    h.exists_mul_eq_of_mem_normalizer_sup hs htS htN (hle t htS htN)
  have h' := h.swap_setting hsS
  have hcc' : Commute c c' := Subgroup.mem_centralizer_iff.mp (h.swap_le_centralizer hs hc'J') c hcJ
  have hsq : ∀ {L : Subgroup (EscapingQuotient z)} (hL : RankOneSetting G S H z L)
      {a : EscapingQuotient z}, a ∈ escapingSylowImage S z → a ∈ L →
      a ^ 2 = 1 ∨ a ^ 2 = escapingBar z := fun hL a haS haL => by
    by_cases ha1 : a ^ 2 = 1
    · exact Or.inl ha1
    · refine Or.inr (hL.unique _ (Subgroup.pow_mem _ haL 2) (orderOf_eq_prime ?_ ha1))
      rw [← pow_mul]
      exact hL.pow_four_eq_one haS haL
  rw [hcc'.mul_pow]
  rcases hsq h hcS hcJ with h1 | h1 <;> rcases hsq h' hc'S hc'J' with h2 | h2 <;>
    rw [h1, h2]
  · exact Or.inl (mul_one 1)
  · exact Or.inr (one_mul _)
  · exact Or.inr (mul_one _)
  · exact Or.inl (by rw [← pow_two, h.bar_sq])

theorem transfer_cond_swap
    {u : (S : Subgroup G)}
    (hu : sylowBar h.square.central u ∉ Subgroup.normalizer (J : Set (EscapingQuotient z)))
    (hu2 : (u : G) ^ 2 = z) {a : G} (haS : a⁻¹ * u * a ∈ (S : Subgroup G)) :
    (u : G)⁻¹ * (a⁻¹ * u * a) ∈ liftToSylow h.square.central
      (escapingSylowImage S z ⊓ Subgroup.normalizer (J : Set (EscapingQuotient z))) := by
  have hz := h.square.central
  set N := Subgroup.normalizer (J : Set (EscapingQuotient z)) with hN
  set u' : (S : Subgroup G) := ⟨a⁻¹ * u * a, haS⟩ with hu'
  have hbarS : ∀ s : (S : Subgroup G), sylowBar hz s ∈ escapingSylowImage S z := fun s => by
    rw [← sylowBar_range hz]
    exact ⟨s, rfl⟩
  have hu'N : sylowBar hz u' ∉ N := by
    intro hN'
    have hinv : orderOf (sylowBar hz u' ^ 2) = 2 := by
      rw [← map_pow, orderOf_sylowBar, Subgroup.coe_pow]
      show orderOf ((a⁻¹ * u * a) ^ 2) = 2
      rw [show (a⁻¹ * u * a) ^ 2 = a⁻¹ * ((u : G) ^ 2) * a by rw [pow_two, pow_two]; group, hu2]
      have := h.square.central.2.1
      rwa [← orderOf_inv_mul_mul_eq z a] at this
    have hz' : sylowBar hz u' ^ 2 = escapingBar z := by
      rcases h.sq_eq_of_mem_normalizer_swap hsS hs hle (hbarS u') hN' with h1 | h1
      · rw [h1, orderOf_one] at hinv
        exact absurd hinv (by decide)
      · exact h1
    rw [← map_pow, sylowBar_eq_bar_iff, Subgroup.coe_pow] at hz'
    change (a⁻¹ * u * a) ^ 2 = z at hz'
    rw [show (a⁻¹ * u * a) ^ 2 = a⁻¹ * ((u : G) ^ 2) * a by rw [pow_two, pow_two]; group, hu2]
      at hz'
    have haM : a ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc a * z = a * (a⁻¹ * z * a) := by rw [hz']
        _ = z * a := by group
    have huM : (u : G) ∈ Subgroup.centralizer ({z} : Set G) := hz.le_centralizer u.2
    have hconj : sylowBar hz u' = (escapingMk z ⟨a, haM⟩)⁻¹ * sylowBar hz u *
        escapingMk z ⟨a, haM⟩ := by
      rw [sylowBar_apply, sylowBar_apply, ← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [hconj] at hN'
    apply hu
    have := (h.normalizer_normal_swap hs).conj_mem _ hN' (escapingMk z ⟨a, haM⟩)
    simpa [mul_assoc] using this
  have h1 : (sylowBar hz u)⁻¹ * sylowBar hz u' ∈ escapingSylowImage S z ⊓ N :=
    ⟨(escapingSylowImage S z).mul_mem ((escapingSylowImage S z).inv_mem (hbarS u)) (hbarS u'),
      h.inv_mul_mem_normalizer_swap hs hu hu'N⟩
  rw [← map_inv, ← map_mul] at h1
  exact (mem_liftToSylow_iff hz (u⁻¹ * u')).mpr h1

end RankOneSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
