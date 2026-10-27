module

public import CFSG.LieType.Ree.SmallReeInvolutionComponents
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotAlternating

public noncomputable section

namespace CFSG.ComponentClassification.OutcomeLocal

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Walter.Ree.Model CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification

section Tools

variable {G : Type*} [Group G]

theorem assembly_isSubnormal_of_normal {H M N : Subgroup G}
    (h : CFSG.Assembly.IsSubnormal H M) (hMN : M ≤ N) (hn : (M.subgroupOf N).Normal) :
    CFSG.Assembly.IsSubnormal H N :=
  h.trans (.step hMN hn (.refl N))

theorem isComponentOf_inf_centralizer_of_normal {Λ Γ B : Subgroup G} (hΛΓ : Λ ≤ Γ)
    (hΛn : (Λ.subgroupOf Γ).Normal) {u : G}
    (hB : CFSG.Assembly.IsComponentOf B (Λ ⊓ centralizer ({u} : Set G))) :
    CFSG.Assembly.IsComponentOf B (Γ ⊓ centralizer ({u} : Set G)) := by
  have hle : Λ ⊓ centralizer ({u} : Set G) ≤ Γ ⊓ centralizer ({u} : Set G) :=
    inf_le_inf_right _ hΛΓ
  refine ⟨hB.1.trans hle, assembly_isSubnormal_of_normal hB.2.1 hle ⟨fun x hx g => ?_⟩, hB.2.2⟩
  rw [mem_subgroupOf] at hx ⊢
  obtain ⟨hxΛ, hxC⟩ := mem_inf.mp hx
  obtain ⟨hgΓ, hgC⟩ := mem_inf.mp g.2
  refine mem_inf.mpr ⟨?_, ?_⟩
  · have h := hΛn.conj_mem ⟨x, hΛΓ hxΛ⟩ (by rw [mem_subgroupOf]; exact hxΛ) ⟨g, hgΓ⟩
    rw [mem_subgroupOf] at h
    exact h
  · exact mul_mem (mul_mem hgC hxC) (inv_mem hgC)

theorem inf_eq_bot_of_commute_of_simple {B₁ B₂ : Subgroup G} (hcomm : ⁅B₁, B₂⁆ = ⊥)
    (hsimple : IsSimpleGroup B₁) (hnab : ∃ x y : B₁, x * y ≠ y * x) : B₁ ⊓ B₂ = ⊥ := by
  have hcent : center B₁ = ⊥ := by
    rcases (center B₁).normal_of_characteristic.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnab
      exact hxy ((mem_center_iff.mp (h ▸ mem_top y)) x)
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx₁, hx₂⟩ := mem_inf.mp hx
  have hxc : (⟨x, hx₁⟩ : B₁) ∈ center B₁ := by
    rw [mem_center_iff]
    intro y
    have h := mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm y.2) x hx₂
    exact Subtype.ext h.symm
  rw [hcent, mem_bot] at hxc
  rw [mem_bot]
  exact congrArg Subtype.val hxc

theorem card_mul_dvd_of_commute {B₁ B₂ Γ : Subgroup G} [Finite Γ] (hcomm : ⁅B₁, B₂⁆ = ⊥)
    (hinf : B₁ ⊓ B₂ = ⊥) (h₁ : B₁ ≤ Γ) (h₂ : B₂ ≤ Γ) :
    Nat.card B₁ * Nat.card B₂ ∣ Nat.card Γ := by
  have hc : ∀ (x : B₁) (y : B₂), Commute (B₁.subtype x) (B₂.subtype y) := fun x y =>
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm x.2) y y.2).symm
  set f := B₁.subtype.noncommCoprod B₂.subtype hc with hfdef
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ hxy
    rw [hfdef, MonoidHom.noncommCoprod_apply] at hxy
    have hx : (x : G) = (y : G)⁻¹ := eq_inv_of_mul_eq_one_left hxy
    have hxB : (x : G) ∈ B₁ ⊓ B₂ := mem_inf.mpr ⟨x.2, hx ▸ inv_mem y.2⟩
    rw [hinf, mem_bot] at hxB
    have hy : (y : G) = 1 := by rw [hxB] at hx; exact inv_eq_one.mp hx.symm
    exact Prod.ext (Subtype.ext hxB) (Subtype.ext hy)
  have hrange : f.range ≤ Γ := by
    rintro _ ⟨⟨x, y⟩, rfl⟩
    rw [hfdef, MonoidHom.noncommCoprod_apply]
    exact mul_mem (h₁ x.2) (h₂ y.2)
  have h1 : Nat.card f.range = Nat.card B₁ * Nat.card B₂ := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  rw [← h1]
  exact Subgroup.card_dvd_of_le hrange

end Tools

theorem false_of_commuting_small_Ree_components (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1))
    {Λ : Subgroup (ModGL ReeTag.G2.tag K)} (hΛΓ : Λ ≤ ReeTag.G2.reeGamma K a)
    (hΛn : (Λ.subgroupOf (ReeTag.G2.reeGamma K a)).Normal) {u₁ u₂ : ModGL ReeTag.G2.tag K}
    (hu₁ : u₁ ∈ Λ) (hu₁2 : orderOf u₁ = 2) (hu₂ : u₂ ∈ Λ) (hu₂2 : orderOf u₂ = 2)
    {B₁ B₂ : Subgroup (ModGL ReeTag.G2.tag K)}
    (hB₁ : CFSG.Assembly.IsComponentOf B₁ (Λ ⊓ centralizer ({u₂} : Set _)))
    (hB₂ : CFSG.Assembly.IsComponentOf B₂ (Λ ⊓ centralizer ({u₁} : Set _)))
    (hcomm : ⁅B₁, B₂⁆ = ⊥) : False := by
  classical
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB₁' := isComponentOf_inf_centralizer_of_normal hΛΓ hΛn hB₁
  have hB₂' := isComponentOf_inf_centralizer_of_normal hΛΓ hΛn hB₂
  obtain ⟨-, hs₁, hn₁, h4₁⟩ :=
    small_Ree_involution_components_simple_two_part_four a K hK (hΛΓ hu₂) hu₂2 hB₁'
  obtain ⟨-, -, -, h4₂⟩ :=
    small_Ree_involution_components_simple_two_part_four a K hK (hΛΓ hu₁) hu₁2 hB₂'
  have hle₁ : B₁ ≤ ReeTag.G2.reeGamma K a := hB₁'.1.trans inf_le_left
  have hle₂ : B₂ ≤ ReeTag.G2.reeGamma K a := hB₂'.1.trans inf_le_left
  have hdvd := card_mul_dvd_of_commute hcomm (inf_eq_bot_of_commute_of_simple hcomm hs₁ hn₁)
    hle₁ hle₂
  have h16 : 2 ^ 4 ∣ Nat.card (ReeTag.G2.reeGamma K a) := by
    have h1 : 4 ∣ Nat.card B₁ := h4₁ ▸ Nat.ordProj_dvd _ _
    have h2 : 4 ∣ Nat.card B₂ := h4₂ ▸ Nat.ordProj_dvd _ _
    exact (show 2 ^ 4 = 4 * 4 by norm_num) ▸ (Nat.mul_dvd_mul h1 h2).trans hdvd
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨-, -, hcard, ⟨P, hP⟩, -, -⟩ := small_Ree_prime_field_involution_fusion a K hK w₀ hw₀
  have hP8 : Nat.card P = 8 := by
    rw [← hcard, ← hP, Subgroup.card_map_of_injective (ReeTag.G2.reeGamma K a).subtype_injective]
  have hmult := P.card_eq_multiplicity
  rw [hP8] at hmult
  have hfact : (Nat.card (ReeTag.G2.reeGamma K a)).factorization 2 = 3 := by
    have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [h8] at hmult
    exact (Nat.pow_right_injective le_rfl hmult).symm
  have hpos : Nat.card (ReeTag.G2.reeGamma K a) ≠ 0 := Nat.card_pos.ne'
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).mp h16
  omega

theorem commuting_block_small_Ree_overgroup_exclusion {G : Type*} [Group G] [Finite G]
    {J : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) (a : ℕ) (k : Type) [Field k] [Finite k]
    [CharP k ReeTag.G2.prime] (hk : Nat.card k = 3 ^ (2 * a + 1)) :
    ¬ Nonempty (L ⧸ center L ≃* ReeTag.G2.reeGamma k a) ∧
      ¬ Nonempty (L ⧸ center L ≃* commutator (ReeTag.G2.reeGamma k a)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hodd, hπKq, hcomm, hloc, -⟩ :=
    escaping_block_quotient_inherits_local_components hq heven hJ hΔ hL hML hLH
  obtain ⟨K₁, hK₁, K₂, hK₂, hne⟩ := hΔ
  have hinv : ∀ K ∈ block J, ∃ t : L, (t : G) ∈ K ∧ orderOf t = 2 := by
    intro K hK
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := centerQuotientImage L K) 2
      (even_iff_two_dvd.1 (hπKq K hK).2)
    obtain ⟨t, htK, ht2, -⟩ := exists_involution_lift_of_odd_center hodd u.2
      (by rw [Subgroup.orderOf_coe, hu])
    exact ⟨t, htK, ht2⟩
  obtain ⟨t₁, ht₁K, ht₁⟩ := hinv K₁ hK₁
  obtain ⟨t₂, ht₂K, ht₂⟩ := hinv K₂ hK₂
  have key : ∀ ψ : L ⧸ center L →* ModGL ReeTag.G2.tag k, Function.Injective ψ →
      ψ.range ≤ ReeTag.G2.reeGamma k a →
      (ψ.range.subgroupOf (ReeTag.G2.reeGamma k a)).Normal → False := by
    intro ψ hψ hΛΓ hΛn
    have hcomp : ∀ K ∈ block J, ∀ K' ∈ block J, K ≠ K' → ∀ t : L, (t : G) ∈ K' →
        orderOf t = 2 → CFSG.Assembly.IsComponentOf ((centerQuotientImage L K).map ψ)
          (ψ.range ⊓ centralizer ({ψ (QuotientGroup.mk' (center L) t)} : Set _)) := by
      intro K hK K' hK' hKK' t htK' ht2
      have h := (isComponentOf_map_iff hψ).2 (hloc K hK K' hK' hKK' t htK' ht2).2
      rwa [map_centralizer_singleton_of_injective hψ] at h
    have hu₁ : orderOf (ψ (QuotientGroup.mk' (center L) t₁)) = 2 := by
      rw [orderOf_injective ψ hψ]
      exact (hloc K₂ hK₂ K₁ hK₁ (Ne.symm hne) t₁ ht₁K ht₁).1
    have hu₂ : orderOf (ψ (QuotientGroup.mk' (center L) t₂)) = 2 := by
      rw [orderOf_injective ψ hψ]
      exact (hloc K₁ hK₁ K₂ hK₂ hne t₂ ht₂K ht₂).1
    refine false_of_commuting_small_Ree_components a k hk hΛΓ hΛn ⟨_, rfl⟩ hu₁ ⟨_, rfl⟩ hu₂
      (hcomp K₁ hK₁ K₂ hK₂ hne t₂ ht₂K ht₂) (hcomp K₂ hK₂ K₁ hK₁ (Ne.symm hne) t₁ ht₁K ht₁) ?_
    rw [← Subgroup.map_commutator, (hcomm K₁ hK₁ K₂ hK₂ hne).2, Subgroup.map_bot]
  refine ⟨fun ⟨e⟩ => ?_, fun ⟨e⟩ => ?_⟩
  ·
    set ψ := (ReeTag.G2.reeGamma k a).subtype.comp e.toMonoidHom with hψdef
    have hψ : Function.Injective ψ :=
      (ReeTag.G2.reeGamma k a).subtype_injective.comp e.injective
    have hrange : ψ.range = ReeTag.G2.reeGamma k a := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact (e x).2
      · intro hy
        exact ⟨e.symm ⟨y, hy⟩, by simp [hψdef]⟩
    refine key ψ hψ hrange.le ⟨fun x _ g => ?_⟩
    rw [mem_subgroupOf, hrange]
    exact (g * x * g⁻¹).2
  ·
    set Γ := ReeTag.G2.reeGamma k a with hΓdef
    set ψ := Γ.subtype.comp ((commutator Γ).subtype.comp e.toMonoidHom) with hψdef
    have hψ : Function.Injective ψ :=
      Γ.subtype_injective.comp ((commutator Γ).subtype_injective.comp e.injective)
    have hrange : ∀ y, y ∈ ψ.range ↔ ∃ c ∈ commutator Γ, (c : ModGL ReeTag.G2.tag k) = y := by
      intro y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨e x, (e x).2, rfl⟩
      · rintro ⟨c, hc, rfl⟩
        exact ⟨e.symm ⟨c, hc⟩, by simp [hψdef]⟩
    have hle : ψ.range ≤ Γ := by
      rintro _ ⟨x, rfl⟩
      exact ((e x : commutator Γ) : Γ).2
    refine key ψ hψ hle ⟨fun x hx g => ?_⟩
    rw [mem_subgroupOf] at hx ⊢
    obtain ⟨c, hc, hcx⟩ := (hrange _).mp hx
    refine (hrange _).mpr ⟨g * c * g⁻¹,
      (inferInstance : (commutator Γ).Normal).conj_mem c hc g, ?_⟩
    have hcx' : c = x := Subtype.ext hcx
    rw [hcx']

end CFSG.ComponentClassification.OutcomeLocal
