module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneRooting
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneIndex

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

namespace RankOneSetting

variable (h : RankOneSetting G S H z J) [J.Normal]
include h

theorem sq_mem_of_mem_sup
    {t : EscapingQuotient z} (htS : t ∈ escapingSylowImage S z)
    (htJK : t ∈ J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z))) :
    t ^ 2 ∈ escapingSylowImage S z ⊓ Subgroup.centralizer (J : Set (EscapingQuotient z)) := by
  obtain ⟨q, hqS, hqJ, c, hcS, hcK, rfl⟩ := h.exists_mul_eq_of_mem_sup htS htJK
  have hqc : Commute q c := Subgroup.mem_centralizer_iff.mp hcK q hqJ
  rw [hqc.mul_pow]
  have hq2 : q ^ 2 ∈ escapingSylowImage S z ⊓
      Subgroup.centralizer (J : Set (EscapingQuotient z)) := by
    refine ⟨(escapingSylowImage S z).pow_mem hqS 2, ?_⟩
    have hq4 : (q ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact h.pow_four_eq_one hqS hqJ
    by_cases hq1 : q ^ 2 = 1
    · rw [hq1]
      exact Subgroup.one_mem _
    · rw [h.unique _ (J.pow_mem hqJ 2) (orderOf_eq_prime hq4 hq1)]
      exact h.quotientData.bar_mem_component_centralizer
  exact Subgroup.mul_mem _ hq2 ⟨(escapingSylowImage S z).pow_mem hcS 2, Subgroup.pow_mem _ hcK 2⟩

theorem inv_mul_mem_inf_sup
    {u v : EscapingQuotient z} (huS : u ∈ escapingSylowImage S z)
    (hvS : v ∈ escapingSylowImage S z)
    (hu : u ∉ escapingSylowImage S z ⊓ (J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z))))
    (hv : v ∉ escapingSylowImage S z ⊓ (J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z)))) :
    u⁻¹ * v ∈ escapingSylowImage S z ⊓ (J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z))) :=
  ⟨(escapingSylowImage S z).mul_mem ((escapingSylowImage S z).inv_mem huS) hvS,
    h.inv_mul_mem_sup_of_not_mem (fun h1 => hu ⟨huS, h1⟩) (fun h1 => hv ⟨hvS, h1⟩)⟩

theorem transfer_cond_of_sq_eq
    {u : (S : Subgroup G)}
    (hu : sylowBar h.square.central u ∉ J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z)))
    (hu2 : (u : G) ^ 2 = z) {a : G} (haS : a⁻¹ * u * a ∈ (S : Subgroup G)) :
    (u : G)⁻¹ * (a⁻¹ * u * a) ∈ liftToSylow h.square.central
      (escapingSylowImage S z ⊓ (J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z)))) := by
  have hz := h.square.central
  set u' : (S : Subgroup G) := ⟨a⁻¹ * u * a, haS⟩ with hu'
  have hbarS : ∀ s : (S : Subgroup G), sylowBar hz s ∈ escapingSylowImage S z := fun s => by
    rw [← sylowBar_range hz]
    exact ⟨s, rfl⟩
  have hu'JK : sylowBar hz u' ∉ J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z)) := by
    intro hJK
    have hsq := h.sq_mem_of_mem_sup (hbarS u') hJK
    have hinv : orderOf (sylowBar hz u' ^ 2) = 2 := by
      rw [← map_pow, orderOf_sylowBar, Subgroup.coe_pow]
      show orderOf ((a⁻¹ * u * a) ^ 2) = 2
      rw [show (a⁻¹ * u * a) ^ 2 = a⁻¹ * ((u : G) ^ 2) * a by rw [pow_two, pow_two]; group, hu2]
      have := h.square.central.2.1
      rwa [← orderOf_inv_mul_mul_eq z a] at this
    have hz' := h.eq_bar_of_mem_centralizer hsq.1 hsq.2 hinv
    rw [← map_pow, sylowBar_eq_bar_iff] at hz'
    rw [Subgroup.coe_pow] at hz'
    change (a⁻¹ * u * a) ^ 2 = z at hz'
    rw [show (a⁻¹ * u * a) ^ 2 = a⁻¹ * ((u : G) ^ 2) * a by rw [pow_two, pow_two]; group,
      hu2] at hz'
    have haM : a ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc a * z = a * (a⁻¹ * z * a) := by rw [hz']
        _ = z * a := by group
    have huM : (u : G) ∈ Subgroup.centralizer ({z} : Set G) := hz.le_centralizer u.2
    have hconj : sylowBar hz u' = (escapingMk z ⟨a, haM⟩)⁻¹ * sylowBar hz u *
        escapingMk z ⟨a, haM⟩ := by
      rw [sylowBar_apply, sylowBar_apply, ← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [hconj] at hJK
    apply hu
    have := (inferInstance :
      (J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z))).Normal).conj_mem
      _ hJK (escapingMk z ⟨a, haM⟩)
    simpa [mul_assoc] using this
  have h1 := h.inv_mul_mem_inf_sup (hbarS u) (hbarS u') (fun h2 => hu h2.2) (fun h2 => hu'JK h2.2)
  rw [← map_inv, ← map_mul] at h1
  exact (mem_liftToSylow_iff hz (u⁻¹ * u')).mpr h1

end RankOneSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
