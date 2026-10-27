module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDOmega
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSocle
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrders

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup MulAction
open scoped Pointwise

theorem not_isPrimePow_136 : ¬ IsPrimePow 136 := fun h => by
  have := (Nat.Coprime.isPrimePow_dvd_mul (by norm_num : Nat.Coprime 8 17) h).1 (by norm_num)
  omega

theorem card_ge_of_two_pretransitive {P Ω : Type*} [Group P] [Finite P] [MulAction P Ω]
    [Finite Ω] (h2 : IsMultiplyPretransitive P Ω 2) {n : ℕ} (hΩ : Nat.card Ω = n) (hn : 2 ≤ n) :
    n * (n - 1) ≤ Nat.card P := by
  classical
  have : Fintype Ω := Fintype.ofFinite Ω
  have hcard : Fintype.card Ω = n := by rw [← Nat.card_eq_fintype_card, hΩ]
  have hne : Nonempty (Fin 2 ↪ Ω) := by
    rw [← Fintype.card_pos_iff, Fintype.card_embedding_eq, Fintype.card_fin, hcard]
    exact Nat.descFactorial_pos.mpr hn
  obtain ⟨x₀⟩ := hne
  have hsurj : Function.Surjective (fun g : P => g • x₀) := fun y => exists_smul_eq P x₀ y
  have hle := Nat.card_le_card_of_surjective _ hsurj
  rwa [Nat.card_eq_fintype_card (α := Fin 2 ↪ Ω), Fintype.card_embedding_eq, Fintype.card_fin,
    hcard, Nat.descFactorial_succ, Nat.descFactorial_one, show n - 1 = n - 1 from rfl,
    mul_comm (n - 1) n] at hle

section LemmaP

theorem false_of_two_pretransitive_136 {P Ω : Type} [Group P] [Finite P] [MulAction P Ω]
    [FaithfulSMul P Ω] [Finite Ω] (hΩ : Nat.card Ω = 136) (h2 : IsMultiplyPretransitive P Ω 2)
    (hdvd : Nat.card P ∣ 2 ^ 11 * 3 ^ 5 * 5 * 17)
    (hcat : ∀ T : Subgroup P, IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
      CFSG.Blueprint.Catalog T) : False := by
  have : Nonempty Ω := (Nat.card_pos_iff.1 (by omega)).1
  have : IsPreprimitive P Ω := isPreprimitive_of_is_two_pretransitive h2
  have h289 : ¬ 17 ^ 2 ∣ Nat.card P := fun h289 => absurd (h289.trans hdvd) (by norm_num)
  obtain ⟨T, hTn, hTs, hTnonab, hTdvd, -, hTc⟩ := Yamada.exists_simple_normal_of_isPreprimitive
    (by norm_num : Nat.Prime 17) (by rw [hΩ]; norm_num) h289 (hΩ ▸ not_isPrimePow_136)
  have hT17 : 17 ∣ Nat.card T := (by norm_num : 17 ∣ 136).trans (hΩ ▸ hTdvd)
  have hTP : Nat.card T ∣ 2 ^ 11 * 3 ^ 5 * 5 * 17 := (card_subgroup_dvd_card T).trans hdvd
  have hA := CatalogOrders.c2_card_mulAut_le (hcat T hTs hTnonab) hTnonab hTP hT17
  have hinj : Function.Injective (MulAut.conjNormal : P →* MulAut T) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : g ∈ centralizer (T : Set P) := by
      rw [mem_centralizer_iff]
      intro x hx
      have := congrArg (fun φ : MulAut T => ((φ ⟨x, hx⟩ : T) : P)) hg
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc x * g = g * x * g⁻¹ * g := by rw [this]
        _ = g * x := by group
    rwa [hTc, mem_bot] at hgc
  have : Finite (MulAut T) :=
    Finite.of_injective (fun φ : MulAut T => (φ : T → T)) fun a b hab => MulEquiv.ext (congrFun hab)
  have hle : Nat.card P ≤ Nat.card (MulAut T) := Nat.card_le_card_of_injective _ hinj
  have hge := card_ge_of_two_pretransitive h2 hΩ (by norm_num)
  omega

end LemmaP

namespace Hyp

variable {G : Type*} [Group G] {d : Data G} (h : Hyp d)
include h

omit h in
theorem exists_omegaPerm_eq (S : d.Om) :
    ∃ x : d.XV, d.omegaPerm x ⟨_, d.tV_mem_Om⟩ = S := by
  obtain ⟨y, hy, hS⟩ := S.2
  refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
  rw [Data.omegaPerm_apply]
  change (fun g => y * g * y⁻¹) '' (d.t • (d.V₁ : Set G)) = S
  rw [conj_image_smul (mem_inf.mp hy).2, hS]

theorem omegaPerm_K₁_fix [Finite G] {k : G} (hk : k ∈ d.K₁) :
    d.omegaPerm ⟨k, h.K₁_le_XV hk⟩ ⟨_, d.tV_mem_Om⟩ = ⟨_, d.tV_mem_Om⟩ := by
  apply Subtype.ext
  rw [Data.omegaPerm_apply]
  change (fun g => k * g * k⁻¹) '' (d.t • (d.V₁ : Set G)) = d.t • (d.V₁ : Set G)
  rw [conj_image_smul (mem_inf.mp (h.K₁_le_XV hk)).2, h.comm_of_mem_L (h.K₁_le_L hk),
    mul_inv_cancel_right]

theorem omegaPerm_K₁_trans [Finite G] (hc : d.Cyc) (S S' : d.Om)
    (hS : S ≠ ⟨_, d.tV_mem_Om⟩) (hS' : S' ≠ ⟨_, d.tV_mem_Om⟩) :
    ∃ (k : G) (hk : k ∈ d.K₁), d.omegaPerm ⟨k, h.K₁_le_XV hk⟩ S = S' := by
  have hp : ∀ {c : G}, c ∈ d.A₁ → ∀ S'' : d.Om, (S'' : Set G) = (c * d.t) • (d.V₁ : Set G) →
      S'' ≠ ⟨_, d.tV_mem_Om⟩ → c ∉ zpowers d.z := by
    intro c hc S'' hS'' hne hcz
    apply hne
    apply Subtype.ext
    rw [hS'']
    have := (h.coset_eq_iff hc (one_mem _)).mpr (by rw [mul_one]; exact inv_mem hcz)
    rwa [one_mul] at this
  obtain ⟨a, ha, ha2, hSa⟩ := h.Om_subset_of_cyc hc S.2
  obtain ⟨b, hb, hb2, hSb⟩ := h.Om_subset_of_cyc hc S'.2
  obtain ⟨k, hk, hkab⟩ := h.K₁_trans a ha ha2 (hp ha S hSa hS) b hb hb2 (hp hb S' hSb hS')
  refine ⟨k, hk, Subtype.ext ?_⟩
  rw [Data.omegaPerm_apply, hSa, conj_image_smul (mem_inf.mp (h.K₁_le_XV hk)).2, hSb]
  have hkaA : k * a * k⁻¹ ∈ d.A₁ := (mem_normalizer_iff.mp (h.CHz_le (mem_inf.mpr
    ⟨h.K₁_cent_z hk, h.L_le_H (h.K₁_le_L hk)⟩)) a).mp ha
  have hkt : k * d.t = d.t * k := h.comm_of_mem_L (h.K₁_le_L hk)
  have hkt' : d.t * k⁻¹ = k⁻¹ * d.t := (Commute.inv_left (show Commute k d.t from hkt)).symm
  rw [show k * (a * d.t) * k⁻¹ = (k * a * k⁻¹) * d.t by
    calc k * (a * d.t) * k⁻¹ = k * a * (d.t * k⁻¹) := by group
      _ = k * a * (k⁻¹ * d.t) := by rw [hkt']
      _ = (k * a * k⁻¹) * d.t := by group]
  exact (h.coset_eq_iff hkaA hb).mpr hkab

omit h in
theorem omegaPerm_inv_apply (x : d.XV) (S : d.Om) : d.omegaPerm x⁻¹ (d.omegaPerm x S) = S := by
  rw [← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one, Equiv.Perm.one_apply]

theorem isMultiplyPretransitive_omega [Finite G] (hc : d.Cyc) :
    MulAction.IsMultiplyPretransitive d.omegaPerm.range d.Om 2 := by
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c e hab hce
  obtain ⟨x, hx⟩ := exists_omegaPerm_eq a
  obtain ⟨y, hy⟩ := exists_omegaPerm_eq c
  have hb' : d.omegaPerm x⁻¹ b ≠ ⟨_, d.tV_mem_Om⟩ := by
    intro he
    apply hab
    rw [← hx, ← he, ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Equiv.Perm.one_apply]
  have he' : d.omegaPerm y⁻¹ e ≠ ⟨_, d.tV_mem_Om⟩ := by
    intro he
    apply hce
    rw [← hy, ← he, ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Equiv.Perm.one_apply]
  obtain ⟨k, hk, hke⟩ := h.omegaPerm_K₁_trans hc _ _ hb' he'
  refine ⟨⟨d.omegaPerm (y * ⟨k, h.K₁_le_XV hk⟩ * x⁻¹), ⟨_, rfl⟩⟩, ?_, ?_⟩
  · change d.omegaPerm (y * ⟨k, h.K₁_le_XV hk⟩ * x⁻¹) a = c
    rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hx,
      omegaPerm_inv_apply, h.omegaPerm_K₁_fix hk, hy]
  · change d.omegaPerm (y * ⟨k, h.K₁_le_XV hk⟩ * x⁻¹) b = e
    rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hke,
      ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]

end Hyp

section V₁Sq

namespace Hyp

variable {G : Type} [Group G] {d : Data G} (h : Hyp d)
include h

theorem V₁_sq_of_ne_top [Finite G] (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hXV : d.XV ≠ ⊤) {v : G} (hv : v ∈ d.V₁) : v * v = 1 := by
  by_contra hne
  have hc : d.Cyc := ⟨v, hv, hne⟩
  have hΩ : Nat.card d.Om = 136 := by rw [Nat.card_coe_set_eq, h.ncard_Om hc]
  refine false_of_two_pretransitive_136 hΩ (h.isMultiplyPretransitive_omega hc)
    (h.card_range_omegaPerm_dvd hc) fun T hT hnonab => ?_
  exact CatalogOrders.catalog_of_kProper_of_le_quotient hK hXV d.omegaPerm.rangeRestrict
    d.omegaPerm.rangeRestrict_surjective T hnonab

theorem V₁_sq [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) {v : G} (hv : v ∈ d.V₁) :
    v * v = 1 := by
  refine h.V₁_sq_of_ne_top hK (fun htop => ?_) hv
  have hN : (d.V₁).Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff]
    exact fun x _ => (show x ∈ d.XV from htop ▸ mem_top x).2
  rcases hN.eq_bot_or_eq_top with hb | ht
  · apply h.z_ne_one
    have := h.z_mem_V₁
    rwa [hb, mem_bot] at this
  · obtain ⟨a, b, hab⟩ := hnonab
    exact hab (h.V₁_comm (ht ▸ mem_top a) (ht ▸ mem_top b))

end Hyp

end V₁Sq

end CFSG.EvenSmallLie.UnitarySix.YamadaD
