module

public import CFSG.LocalAnalysis.ComponentInitial.DerivedFixedLayer
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification

theorem map_centralizer_center_quotient {L : Type*} [Group L]
    (hodd : Odd (Nat.card (center L))) {t : L} (ht : t ^ 2 = 1) :
    (centralizer ({t} : Set L)).map (QuotientGroup.mk' (center L)) =
      centralizer ({QuotientGroup.mk' (center L) t} : Set (L ⧸ center L)) := by
  apply le_antisymm
  · rintro _ ⟨l, hl, rfl⟩
    rw [mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff.1 hw, ← map_mul, ← map_mul, mem_centralizer_iff.1 hl t rfl]
  · intro x hx
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (center L) x
    have hcZ : l * t * l⁻¹ * t⁻¹ ∈ center L := by
      have h1 := mem_centralizer_iff.1 hx _ (Set.mem_singleton _)
      rw [← QuotientGroup.eq_one_iff]
      change QuotientGroup.mk' (center L) (l * t * l⁻¹ * t⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
      group
    have hcomm : Commute (l * t * l⁻¹ * t⁻¹) t := (mem_center_iff.1 hcZ t).symm
    have hc2 : (l * t * l⁻¹ * t⁻¹) ^ 2 = 1 := by
      have h1 := hcomm.mul_pow 2
      have h2 : (l * t * l⁻¹) ^ 2 = 1 := by
        rw [show l * t * l⁻¹ = (MulAut.conj l) t by simp, ← map_pow, ht, map_one]
      rw [show l * t * l⁻¹ * t⁻¹ * t = l * t * l⁻¹ by group, h2, ht, mul_one] at h1
      exact h1.symm
    have hc1 : l * t * l⁻¹ * t⁻¹ = 1 := by
      have hdvd : orderOf (⟨_, hcZ⟩ : center L) ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one]
        exact Subtype.ext (by simpa using hc2)
      have h1 := Nat.dvd_gcd hdvd (orderOf_dvd_natCard (⟨_, hcZ⟩ : center L))
      rw [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.2 hodd), Nat.dvd_one,
        orderOf_eq_one_iff] at h1
      exact congrArg Subtype.val h1
    refine ⟨l, mem_centralizer_iff.2 fun w hw => ?_, rfl⟩
    rw [Set.mem_singleton_iff.1 hw]
    calc t * l = l * t * l⁻¹ * t⁻¹ * (t * l) := by rw [hc1, one_mul]
      _ = l * t := by group

theorem orderOf_mk_center_eq_two {L : Type*} [Group L] (hodd : Odd (Nat.card (center L)))
    {t : L} (ht : orderOf t = 2) : orderOf (QuotientGroup.mk' (center L) t) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, ← ht, pow_orderOf_eq_one, map_one]
  · intro h
    have htZ : t ∈ center L := by
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    have h2 := orderOf_dvd_natCard (⟨t, htZ⟩ : center L)
    rw [Subgroup.orderOf_mk, ht] at h2
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)

theorem map_subtype_centralizer_singleton {G : Type*} [Group G] (L : Subgroup G) (t : L) :
    (centralizer ({t} : Set L)).map L.subtype = L ⊓ centralizer ({(t : G)} : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine mem_inf.2 ⟨y.2, mem_centralizer_iff.2 fun w hw => ?_⟩
    rw [Set.mem_singleton_iff.1 hw]
    exact congrArg Subtype.val (mem_centralizer_iff.1 hy t rfl)
  · intro hx
    obtain ⟨hxL, hxc⟩ := mem_inf.1 hx
    refine ⟨⟨x, hxL⟩, mem_centralizer_iff.2 fun w hw => ?_, rfl⟩
    rw [Set.mem_singleton_iff.1 hw]
    exact Subtype.ext (mem_centralizer_iff.1 hxc (t : G) rfl)

variable {G : Type*} [Group G] [Finite G]

abbrev centerQuotientImage (L K : Subgroup G) : Subgroup (L ⧸ center L) :=
  (K.subgroupOf L).map (QuotientGroup.mk' (center L))

theorem escaping_block_quotient_inherits_local_components {J : Subgroup G}
    (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (_hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) :
    Odd (Nat.card (center L)) ∧
      (∀ K ∈ block J, CFSG.Assembly.IsQuasisimple (centerQuotientImage L K) ∧
        Even (Nat.card (centerQuotientImage L K))) ∧
      (∀ K₁ ∈ block J, ∀ K₂ ∈ block J, K₁ ≠ K₂ →
        centerQuotientImage L K₁ ≠ centerQuotientImage L K₂ ∧
          ⁅centerQuotientImage L K₁, centerQuotientImage L K₂⁆ = ⊥) ∧
      (∀ K₁ ∈ block J, ∀ K₂ ∈ block J, K₁ ≠ K₂ → ∀ t : L, (t : G) ∈ K₂ → orderOf t = 2 →
        orderOf (QuotientGroup.mk' (center L) t) = 2 ∧
          CFSG.Assembly.IsComponentOf (centerQuotientImage L K₁)
            (centralizer ({QuotientGroup.mk' (center L) t} : Set (L ⧸ center L)))) ∧
      ∃ u : L ⧸ center L, orderOf u = 2 ∧ ∃ Q : Subgroup (L ⧸ center L),
        CFSG.Assembly.IsComponentOf Q (centralizer ({u} : Set (L ⧸ center L))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKL : ∀ K ∈ block J, K ≤ L := fun K hK => (le_blockGroup hK).trans hML
  have hodd : Odd (Nat.card (center L)) := by
    rw [← Nat.not_even_iff_odd]
    intro hev
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center L) 2 (even_iff_two_dvd.1 hev)
    have hz2 : orderOf ((z : L) : G) = 2 := by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
    have hzJ : ((z : L) : G) ∈ centralizer (J : Set G) := by
      rw [mem_centralizer_iff]
      intro j hj
      exact congrArg Subtype.val (mem_center_iff.1 z.2 ⟨j, hKL J mem_block_self hj⟩)
    apply hLH
    refine le_trans ?_ (centralizer_le_normalizer_blockGroup hJ heven mem_block_self hzJ hz2)
    intro l hl
    rw [mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff.1 hw]
    exact (congrArg Subtype.val (mem_center_iff.1 z.2 ⟨l, hl⟩)).symm
  have hKq : ∀ K ∈ block J, CFSG.Assembly.IsQuasisimple K := fun K hK =>
    isQuasisimple_of_isConjOf hq hK.1
  have hKsub : ∀ K ∈ block J, CFSG.IsQuasisimple (K.subgroupOf L) := fun K hK =>
    (isQuasisimple_congr (subgroupOfEquivOfLe (hKL K hK))).2
      ((AssemblyBPredicates.isQuasisimple_iff_native K).1 (hKq K hK))
  have hKnc : ∀ K ∈ block J, ¬ K.subgroupOf L ≤ (QuotientGroup.mk' (center L)).ker :=
    fun K hK h => by
      rw [QuotientGroup.ker_mk'] at h
      apply not_le_centralizer_self_of_isQuasisimple (hKq K hK)
      intro x hx
      rw [mem_centralizer_iff]
      intro y hy
      have hxc : (⟨x, hKL K hK hx⟩ : L) ∈ center L := h (Subgroup.mem_subgroupOf.2 hx)
      exact congrArg Subtype.val (mem_center_iff.1 hxc ⟨y, hKL K hK hy⟩)
  have hπKq : ∀ K ∈ block J, CFSG.Assembly.IsQuasisimple (centerQuotientImage L K) :=
    fun K hK => (AssemblyBPredicates.isQuasisimple_iff_native _).2
      (CFSG.LocalCores.isQuasisimple_map (hKsub K hK) _ (hKnc K hK))
  have hKeven : ∀ K ∈ block J, Even (Nat.card K) := fun K hK => by
    obtain ⟨g, rfl⟩ := hK.1
    rwa [card_conjSub]
  have hinvK : ∀ K ∈ block J, ∃ t : L, (t : G) ∈ K ∧ orderOf t = 2 := fun K hK => by
    obtain ⟨k, hk⟩ :=
      exists_prime_orderOf_dvd_card' (G := K) 2 (even_iff_two_dvd.1 (hKeven K hK))
    exact ⟨⟨k, hKL K hK k.2⟩, k.2, by rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hk]⟩
  have hcommL : ∀ K₁ ∈ block J, ∀ K₂ ∈ block J, K₁ ≠ K₂ →
      ⁅K₁.subgroupOf L, K₂.subgroupOf L⁆ = ⊥ := fun K₁ hK₁ K₂ hK₂ hne => by
    have h := (commRel_of_mem_block hJ heven hK₁ hK₂).resolve_left hne
    apply (Subgroup.map_injective L.subtype_injective)
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le (hKL K₁ hK₁),
      Subgroup.map_subgroupOf_eq_of_le (hKL K₂ hK₂), Subgroup.map_bot, h]
  have hcommπ : ∀ K₁ ∈ block J, ∀ K₂ ∈ block J, K₁ ≠ K₂ →
      ⁅centerQuotientImage L K₁, centerQuotientImage L K₂⁆ = ⊥ := fun K₁ hK₁ K₂ hK₂ hne => by
    rw [centerQuotientImage, centerQuotientImage, ← Subgroup.map_commutator,
      hcommL K₁ hK₁ K₂ hK₂ hne, Subgroup.map_bot]
  have hloc : ∀ K₁ ∈ block J, ∀ K₂ ∈ block J, K₁ ≠ K₂ → ∀ t : L, (t : G) ∈ K₂ →
      orderOf t = 2 →
      orderOf (QuotientGroup.mk' (center L) t) = 2 ∧
        CFSG.Assembly.IsComponentOf (centerQuotientImage L K₁)
          (centralizer ({QuotientGroup.mk' (center L) t} : Set (L ⧸ center L))) := by
    intro K₁ hK₁ K₂ hK₂ hne t htK ht
    refine ⟨orderOf_mk_center_eq_two hodd ht, ?_⟩
    have ht2 : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe, ht]
    have htc : (t : G) ∈ centralizer (K₁ : Set G) := by
      have h := (commRel_of_mem_block hJ heven hK₁ hK₂).resolve_left hne
      rw [mem_centralizer_iff]
      intro k hk
      exact commute_of_commutator_eq_bot' h hk htK
    obtain ⟨c, hc⟩ := hK₁.1
    have hK₁u : IsUniversalComponent K₁ := by rw [hc]; exact isUniversalComponent_conjSub hJ c
    have hcomp := hK₁u t htc ht2
    have hcompL : CFSG.Assembly.IsComponentOf K₁ (L ⊓ centralizer ({(t : G)} : Set G)) :=
      isComponentOf_of_le hcomp (le_inf (hKL K₁ hK₁) hcomp.1) inf_le_right
    rw [← map_subtype_centralizer_singleton,
      ← Subgroup.map_subgroupOf_eq_of_le (hKL K₁ hK₁)] at hcompL
    have hcomp' := (isComponentOf_map_iff L.subtype_injective).1 hcompL
    have ht2' : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
    rw [← map_centralizer_center_quotient hodd ht2']
    exact ⟨map_mono hcomp'.1, assembly_isSubnormal_map _ hcomp'.2.1, hπKq K₁ hK₁⟩
  refine ⟨hodd, fun K hK => ⟨hπKq K hK, ?_⟩, fun K₁ hK₁ K₂ hK₂ hne => ⟨?_, hcommπ K₁ hK₁ K₂ hK₂ hne⟩,
    hloc, ?_⟩
  ·
    obtain ⟨t, htK, ht⟩ := hinvK K hK
    have hmem : QuotientGroup.mk' (center L) t ∈ centerQuotientImage L K :=
      ⟨t, Subgroup.mem_subgroupOf.2 htK, rfl⟩
    have h2 := orderOf_dvd_natCard (⟨_, hmem⟩ : centerQuotientImage L K)
    rw [Subgroup.orderOf_mk, orderOf_mk_center_eq_two hodd ht] at h2
    exact even_iff_two_dvd.2 h2
  · intro h
    have hc := hcommπ K₁ hK₁ K₂ hK₂ hne
    rw [← h, commutator_self_of_isQuasisimple (hπKq K₁ hK₁)] at hc
    exact not_le_centralizer_self_of_isQuasisimple (hπKq K₁ hK₁) (by rw [hc]; exact bot_le)
  · obtain ⟨K₁, hK₁, K₂, hK₂, hne⟩ := hΔ
    obtain ⟨t, htK, ht⟩ := hinvK K₂ hK₂
    obtain ⟨h1, h2⟩ := hloc K₁ hK₁ K₂ hK₂ hne t htK ht
    exact ⟨_, h1, _, h2⟩

end CFSG.LocalAnalysis.ComponentInitial
