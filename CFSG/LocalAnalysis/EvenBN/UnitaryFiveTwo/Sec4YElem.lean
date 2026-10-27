module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4WCycAct
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.CatalogSeven
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSocle

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup MulAction CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD

theorem not_isPrimePow_twentyEight : ¬ IsPrimePow 28 := fun h => by
  have := (Nat.Coprime.isPrimePow_dvd_mul (by norm_num : Nat.Coprime 4 7) h).1 (by norm_num)
  omega

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem XW_ne_top
    (h : d.Hyp) :
    d.XW ≠ ⊤ := by
  intro htop
  have hN : d.W.Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff]
    exact fun x _ => (Subgroup.mem_inf.1 (show x ∈ d.XW from htop ▸ mem_top x)).2
  have := h.simple
  rcases hN.eq_bot_or_eq_top with hb | ht
  · have hc := h.sec4_9_W.1
    rw [hb, Subgroup.card_bot] at hc
    exact absurd hc (by norm_num)
  · obtain ⟨a, b, hab⟩ := h.nonab
    exact hab (h.sec4_9_W.2.2.2.2.1 a (ht ▸ mem_top a) b (ht ▸ mem_top b))

end Data.Hyp

section C7

theorem false_of_two_pretransitive_28 {P Ω : Type} [Group P] [Finite P] [MulAction P Ω]
    [FaithfulSMul P Ω] [Finite Ω] (hΩ : Nat.card Ω = 28) (h2 : IsMultiplyPretransitive P Ω 2)
    (hdvd : Nat.card P ∣ 2 ^ 16 * 3 ^ 4 * 7) (h81 : 81 ∣ Nat.card P)
    (hcat : ∀ T : Subgroup P, IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
      CFSG.Blueprint.Catalog T) : False := by
  have : Nonempty Ω := (Nat.card_pos_iff.1 (by omega)).1
  have : IsPreprimitive P Ω := isPreprimitive_of_is_two_pretransitive h2
  have h49 : ¬ 7 ^ 2 ∣ Nat.card P := fun h49 => absurd (h49.trans hdvd) (by norm_num)
  obtain ⟨T, hTn, hTs, hTnonab, hTdvd, -, hTc⟩ :=
    CFSG.EvenSmallLie.UnitarySix.Yamada.exists_simple_normal_of_isPreprimitive
      (by norm_num : Nat.Prime 7) (by rw [hΩ]; norm_num) h49 (hΩ ▸ not_isPrimePow_twentyEight)
  have hT7 : 7 ∣ Nat.card T := (by norm_num : 7 ∣ 28).trans (hΩ ▸ hTdvd)
  have hTP : Nat.card T ∣ 2 ^ 16 * 3 ^ 4 * 7 := (card_subgroup_dvd_card T).trans hdvd
  have hA := CFSG.EvenSmallLie.CatalogOrders.c7_not_dvd_card_mulAut (hcat T hTs hTnonab) hTnonab
    hTP hT7
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
  apply hA
  refine h81.trans ?_
  rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact card_subgroup_dvd_card _

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem false_of_cyc
    (h : d.Hyp)
    (hc : d.CycW) : False := by
  have hΩ := h.card_OmW hc
  have : Finite d.OmW := Nat.finite_of_card_ne_zero (by omega)
  refine false_of_two_pretransitive_28 hΩ (h.isMultiplyPretransitive_omegaW hc)
    (h.card_range_omegaPermW_dvd hc) (h.eightyOne_dvd_card_range hc) fun T hT hnonab => ?_
  exact CFSG.EvenSmallLie.CatalogOrders.catalog_of_kProper_of_le_quotient
    h.setting.setting.kProper h.XW_ne_top d.omegaPermW.rangeRestrict
    d.omegaPermW.rangeRestrict_surjective T hnonab

theorem Y_sq
    (h : d.Hyp) {y : G}
    (hy : y ∈ d.Y) : y * y = 1 := by
  by_contra hy2
  rcases h.omega_Y_cases with hF | hE
  · refine h.false_of_cyc ?_
    by_contra hnc
    have hall : ∀ w ∈ d.W, w * w = 1 := fun w hw => by
      by_contra hw2
      exact hnc ⟨w, hw, hw2⟩
    have hle : d.W ≤ d.ZX₄ := fun w hw =>
      h.mem_ZX₄_of_mem_W_of_mem_F hw (hF w (d.W_le_Y hw) (hall w hw))
    have := Subgroup.card_le_of_le hle
    rw [h.sec4_9_W.1, Data.ZX₄, d.card_pull, card_ZX₄sub] at this
    exact absurd this (by norm_num)
  · exact hy2 (hE y hy)

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
