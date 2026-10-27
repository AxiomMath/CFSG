module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnbalInner

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G] {J : Subgroup G} {q : Jhat J →* Equiv.Perm (Fin 42)}

theorem comm_of_simple_range {x : G} {C : Subgroup (Equiv.Perm (Fin 42))} [IsSimpleGroup C]
    (hrange : (phiC J x q).range = C)
    (h2 : 2 ∣ Nat.card C) {d : G} (hdN : d ∈ normalizer (J : Set G))
    (hd : d ∈ (pPrimeCore 2 (centralizer ({x} : Set G))).map
      (centralizer ({x} : Set G)).subtype)
    {ρ : Equiv.Perm (Fin 42)} (hρ : ∀ e, q (betaHat J hdN e) = ρ * q e * ρ⁻¹) :
    ∀ t ∈ C, ρ * t = t * ρ := by
  set Od := (pPrimeCore 2 (centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype
  set O' := ((Od ⊓ J).subgroupOf (J ⊓ centralizer ({x} : Set G))).map (phiC J x q) with hO'
  have hO'C : O' ≤ C := by
    rw [← hrange]
    exact map_le_range _ _
  have hodd : ∀ u ∈ O', Nat.Coprime 2 (orderOf u) := by
    rintro _ ⟨o, ho, rfl⟩
    have ho' : (o : G) ∈ Od := (mem_inf.mp (mem_subgroupOf.mp ho)).1
    have h1 := orderOf_map_dvd (phiC J x q) o
    rw [← Subgroup.orderOf_coe] at h1
    exact (coprime_orderOf_of_mem_oddCore ho').coprime_dvd_right h1
  have hnormal : (O'.subgroupOf C).Normal := by
    constructor
    intro u hu t
    rw [mem_subgroupOf] at hu ⊢
    obtain ⟨o, ho, hou⟩ := hu
    have ht : (t : Equiv.Perm (Fin 42)) ∈ (phiC J x q).range := hrange ▸ t.2
    obtain ⟨m, hm⟩ := ht
    have ho' := mem_subgroupOf.mp ho
    obtain ⟨hoO, hoJ⟩ := mem_inf.mp ho'
    have hmo : (m : G) * o * (m : G)⁻¹ ∈ Od ⊓ J :=
      mem_inf.mpr ⟨conj_mem_oddCore m.2.2 hoO, J.mul_mem (J.mul_mem m.2.1 hoJ) (J.inv_mem m.2.1)⟩
    refine ⟨m * o * m⁻¹, mem_subgroupOf.mpr hmo, ?_⟩
    rw [map_mul, map_mul, map_inv, hm, hou]
    rfl
  have hbot : O' = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (O'.subgroupOf C) with h | h
    · rw [eq_bot_iff]
      intro u hu
      have : (⟨u, hO'C hu⟩ : C) ∈ O'.subgroupOf C := mem_subgroupOf.mpr hu
      rw [h, mem_bot] at this
      exact mem_bot.mpr (congrArg Subtype.val this)
    · exfalso
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2
      have hg' : g ∈ O'.subgroupOf C := by rw [h]; exact mem_top g
      have := hodd _ (mem_subgroupOf.mp hg')
      rw [Subgroup.orderOf_coe, hg] at this
      exact absurd this (by norm_num)
  intro t ht
  have ht' : t ∈ (phiC J x q).range := hrange ▸ ht
  obtain ⟨c, rfl⟩ := ht'
  have hcJ := c.2.1
  have hcx := c.2.2
  have hm : (c : G)⁻¹ * d⁻¹ * c * d ∈ J := by
    have := conj_mem_of_mem_normalizer hdN hcJ
    rw [show (c : G)⁻¹ * d⁻¹ * c * d = (c : G)⁻¹ * (d⁻¹ * c * d) by group]
    exact J.mul_mem (J.inv_mem hcJ) this
  have hmo := comm_mem_oddCore hcx hd
  have hmx := mem_centralizer_of_mem_oddCore hmo
  have hu : phiC J x q ⟨_, hm, hmx⟩ ∈ O' :=
    ⟨⟨_, hm, hmx⟩, mem_subgroupOf.mpr (mem_inf.mpr ⟨hmo, hm⟩), rfl⟩
  rw [hbot, mem_bot] at hu
  have hu' := image_comm_eq hdN hρ hcJ hm
  have e1 : phiC J x q ⟨_, hm, hmx⟩ = q (jq J ⟨_, hm⟩) := rfl
  rw [← e1, hu] at hu'
  have e2 : phiC J x q c = q (jq J ⟨c, hcJ⟩) := rfl
  rw [e2]
  generalize q (jq J ⟨c, hcJ⟩) = s at hu' ⊢
  calc ρ * s = s * (s⁻¹ * ρ * s * ρ⁻¹) * ρ := by group
    _ = s * ρ := by rw [← hu', mul_one]


theorem false_of_field_graph
    (hL : IsL34Type (J ⧸ Open.fusionZStar J)) {x : G} (hxN : x ∈ normalizer (J : Set G))
    (hx2 : x * x = 1) (hqS : ∀ e, q e ∈ S) (hqsurj : ∀ s ∈ S, ∃ e, q e = s)
    (hqker : q.ker = center (Jhat J)) {ρ₀ : Equiv.Perm (Fin 42)} (hρ₀ : ρ₀ = r₂ ∨ ρ₀ = r₃)
    (hβ : ∀ e, q (betaHat J hxN e) = ρ₀ * q e * ρ₀⁻¹) {D : Set G}
    (hDJ : closure {y | ∃ j ∈ J, ∃ d ∈ D, y = j⁻¹ * d⁻¹ * j * d} = J)
    (hDo : ∀ d ∈ D, d ∈ (pPrimeCore 2 (centralizer ({x} : Set G))).map
      (centralizer ({x} : Set G)).subtype) : False := by
  have hDN := fun d (hd : d ∈ D) => mem_normalizer_of_closure hDJ hd
  have hρ₀R : ρ₀ ∈ R := by rcases hρ₀ with rfl | rfl <;> simp [r₂_mem_R, r₃_mem_R]
  have hρ₀2 : ρ₀ * ρ₀ = 1 := by rcases hρ₀ with rfl | rfl <;> simp [r₂_mul_self, r₃_mul_self]
  have hρ₀1 : ρ₀ ≠ 1 := by
    rcases hρ₀ with rfl | rfl
    · exact fun h => not_mem_S_r₂ (h ▸ S.one_mem)
    · exact fun h => not_mem_S_r₃ (h ▸ S.one_mem)
  refine false_of_closure_le hL hDJ fun d hd j hj => ?_
  obtain ⟨ρ, hρR, hρ⟩ := exists_realization q hqS hqsurj (betaHat J (hDN d hd)) (fun e => by
    rw [hqker]
    exact mulEquiv_mem_center_iff _ e)
  have hxd : x * d = d * x :=
    (mem_centralizer_singleton_iff.mp (mem_centralizer_of_mem_oddCore (hDo d hd))).symm
  have hρr := realization_comm hqsurj hxN (hDN d hd) hxd hρ₀R hρR hβ hρ
  have h945 := realization_pow_odd hqsurj (hDN d hd)
    (coprime_orderOf_of_mem_oddCore (hDo d hd)) hρR hρ
  have hcases : ρ = 1 ∨ ρ = ρ₀ := by
    rcases hρ₀ with rfl | rfl
    · have : IsSimpleGroup C₂ := isSimpleGroup_C₂
      have hrange : (phiC J x q).range = C₂ := le_antisymm (range_le_of_realization hxN hqS hβ)
        (le_range_of_perfect hxN hx2 hqsurj hqker hβ
          (commutator_eq_of_simple (C := C₂) exists_mul_ne_C₂))
      exact eq_of_commute_C₂ hρR hρr.symm (comm_of_simple_range (C := C₂) hrange
        (by rw [card_C₂]; norm_num) (hDN d hd) (hDo d hd) hρ)
    · have : IsSimpleGroup C₃ := isSimpleGroup_C₃
      have hrange : (phiC J x q).range = C₃ := le_antisymm (range_le_of_realization hxN hqS hβ)
        (le_range_of_perfect hxN hx2 hqsurj hqker hβ
          (commutator_eq_of_simple (C := C₃) exists_mul_ne_C₃))
      exact eq_of_commute_C₃ hρR hρr.symm (comm_of_simple_range (C := C₃) hrange
        (by rw [card_C₃]; norm_num) (hDN d hd) (hDo d hd) hρ)
  have hρ1 : ρ = 1 := by
    rcases hcases with h | h
    · exact h
    · exfalso
      apply hρ₀1
      have h1 : ρ₀ ^ 945 = ρ₀ := by
        have : ρ₀ ^ 945 = (ρ₀ * ρ₀) ^ 472 * ρ₀ := by
          rw [← pow_two, ← pow_mul, ← pow_succ]
        rw [this, hρ₀2, one_pow, one_mul]
      rw [← h1, ← h, h945]
  refine comm_mem_zStarIn_of_realization hqker (hDN d hd) (fun e => ?_) hj
  rw [hρ e, hρ1]
  group

end CFSG.ComponentClassification.GrSLit.L34Facts
