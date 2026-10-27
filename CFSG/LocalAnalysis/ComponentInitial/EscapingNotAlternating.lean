module

public import CFSG.LocalAnalysis.ComponentInitial.EscapingBlockQuotient
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingLocalComponents

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification

universe u

theorem map_centralizer_singleton_of_injective {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) (u : G) :
    (centralizer ({u} : Set G)).map f = f.range ⊓ centralizer ({f u} : Set H) := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨⟨g, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hg]
  · rintro ⟨⟨g, rfl⟩, hy⟩
    refine ⟨g, Subgroup.mem_centralizer_singleton_iff.2 (hf ?_), rfl⟩
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_singleton_iff.1 hy

theorem isQuasisimple_map_of_injective {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) {Q : Subgroup G} (hQ : CFSG.Assembly.IsQuasisimple Q) :
    CFSG.Assembly.IsQuasisimple (Q.map f) := by
  rw [AssemblyBPredicates.isQuasisimple_iff_native] at hQ ⊢
  exact (isQuasisimple_congr (Q.equivMapOfInjective f hf)).1 hQ

theorem exists_involution_lift_of_odd_center {G : Type*} [Group G] [Finite G] {L K : Subgroup G}
    (hodd : Odd (Nat.card (center L))) {u : L ⧸ center L} (hu : u ∈ centerQuotientImage L K)
    (hu2 : orderOf u = 2) :
    ∃ t : L, (t : G) ∈ K ∧ orderOf t = 2 ∧ QuotientGroup.mk' (center L) t = u := by
  obtain ⟨x, hxK, rfl⟩ := hu
  have hn : 2 ∣ orderOf x := by
    rw [← hu2]
    exact orderOf_map_dvd _ x
  have hn0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  have hx2 : x ^ 2 ∈ center L := by
    rw [← QuotientGroup.eq_one_iff]
    have h := pow_orderOf_eq_one (QuotientGroup.mk' (center L) x)
    rwa [hu2, ← map_pow, QuotientGroup.mk'_apply] at h
  have hdodd : Odd (orderOf x / 2) := by
    rw [← orderOf_pow_of_dvd two_ne_zero hn]
    have h := orderOf_dvd_natCard (⟨x ^ 2, hx2⟩ : center L)
    rw [Subgroup.orderOf_mk] at h
    exact hodd.of_dvd_nat h
  refine ⟨x ^ (orderOf x / 2), (K.subgroupOf L).pow_mem hxK _, ?_, ?_⟩
  · rw [orderOf_pow_of_dvd hdodd.pos.ne' (Nat.div_dvd_of_dvd hn), Nat.div_div_self hn hn0]
  · obtain ⟨k, hk⟩ := hdodd
    have h1 : QuotientGroup.mk' (center L) x ^ 2 = 1 := by
      rw [← hu2]
      exact pow_orderOf_eq_one _
    rw [map_pow, hk, pow_succ, pow_mul, h1, one_pow, one_mul]

theorem commuting_block_escaping_quasisimple_overgroup_not_alternating {G : Type*} [Group G]
    [Finite G] {J : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J)
    (heven : Even (Nat.card J)) (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial)
    {L : Subgroup G} (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) :
    Odd (Nat.card (centralizer (L : Set G))) ∧ Odd (Nat.card (center L)) ∧
      ∀ (Ω : Type u) [Fintype Ω] [DecidableEq Ω], 5 ≤ Nat.card Ω →
        ¬ Nonempty (L ⧸ center L ≃* alternatingGroup Ω) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hodd, hπKq, hcomm, hloc, -⟩ :=
    escaping_block_quotient_inherits_local_components hq heven hJ hΔ hL hML hLH
  refine ⟨?_, hodd, fun Ω _ _ _ ⟨e⟩ => ?_⟩
  ·
    rw [← Nat.not_even_iff_odd]
    intro hev
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := centralizer (L : Set G)) 2
      (even_iff_two_dvd.1 hev)
    have hz2 : orderOf (z : G) = 2 := by rw [Subgroup.orderOf_coe, hz]
    have hzJ : (z : G) ∈ centralizer (J : Set G) :=
      Subgroup.centralizer_le ((le_blockGroup mem_block_self).trans hML) z.2
    apply hLH
    refine le_trans ?_ (centralizer_le_normalizer_blockGroup hJ heven mem_block_self hzJ hz2)
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 z.2 l hl)
  ·
    obtain ⟨K₁, hK₁, K₂, hK₂, hne⟩ := hΔ
    let ψ : L ⧸ center L →* Equiv.Perm Ω := (alternatingGroup Ω).subtype.comp e.toMonoidHom
    have hψ : Function.Injective ψ := (alternatingGroup Ω).subtype_injective.comp e.injective
    have hψrange : ψ.range = alternatingGroup Ω := by
      ext σ
      constructor
      · rintro ⟨w, rfl⟩
        exact (e w).2
      · intro hσ
        exact ⟨e.symm ⟨σ, hσ⟩, by simp [ψ]⟩
    have hlocal : ∀ K ∈ block J, ∀ K' ∈ block J, K ≠ K' →
        ∀ t ∈ (centerQuotientImage L K').map ψ, orderOf t = 2 →
          CFSG.Assembly.IsComponentOf ((centerQuotientImage L K).map ψ)
            (alternatingGroup Ω ⊓ centralizer ({t} : Set (Equiv.Perm Ω))) := by
      intro K hK K' hK' hKK' t ht ht2
      obtain ⟨w, hw, rfl⟩ := ht
      rw [orderOf_injective ψ hψ] at ht2
      obtain ⟨t₀, ht₀K, ht₀2, rfl⟩ := exists_involution_lift_of_odd_center hodd hw ht2
      have h := (isComponentOf_map_iff hψ).2 (hloc K hK K' hK' hKK' t₀ ht₀K ht₀2).2
      rwa [map_centralizer_singleton_of_injective hψ, hψrange] at h
    refine alternating_commuting_universal_pair_exclusion (T := alternatingGroup Ω) le_rfl
      ⟨(centerQuotientImage L K₁).map ψ, (centerQuotientImage L K₂).map ψ,
        (Subgroup.map_le_range ψ _).trans hψrange.le,
        (Subgroup.map_le_range ψ _).trans hψrange.le,
        isQuasisimple_map_of_injective hψ (hπKq K₁ hK₁).1,
        isQuasisimple_map_of_injective hψ (hπKq K₂ hK₂).1, ?_, ?_, ?_,
        hlocal K₁ hK₁ K₂ hK₂ hne, hlocal K₂ hK₂ K₁ hK₁ (Ne.symm hne)⟩
    · rw [Subgroup.card_map_of_injective hψ]
      exact (hπKq K₁ hK₁).2
    · rw [Subgroup.card_map_of_injective hψ]
      exact (hπKq K₂ hK₂).2
    · rw [← Subgroup.map_commutator, (hcomm K₁ hK₁ K₂ hK₂ hne).2, Subgroup.map_bot]

end CFSG.LocalAnalysis.ComponentInitial
