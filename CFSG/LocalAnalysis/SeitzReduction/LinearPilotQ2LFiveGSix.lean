module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveGNorm
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixWStd

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

section Bar

variable {G : Type} [Group G] [Finite G]

theorem centralizer_mk_le_sup_of_normalizer_inf_le {W V L₁ : Subgroup G} {t : G}
    (ht2 : t * t = 1) (hW2 : ∀ w ∈ W, w * w = 1)
    (hcard : Nat.card W = Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2)
    (hWt : W ⊓ centralizer ({t} : Set G) = V) (htW : t ∈ normalizer (W : Set G))
    (hLW : L₁ ≤ normalizer (W : Set G))
    (hNV : normalizer (V : Set G) ⊓ centralizer ({t} : Set G) ≤ V ⊔ L₁ ⊔ zpowers t) :
    centralizer ({QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))) ⟨t, htW⟩} :
        Set (normalizer (W : Set G) ⧸ W.subgroupOf (normalizer (W : Set G)))) ≤
      (L₁.subgroupOf (normalizer (W : Set G))).map
          (QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G)))) ⊔
        zpowers (QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))) ⟨t, htW⟩) := by
  set ν := QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))) with hν
  have hsurj := tcomm_surjective_of_card hW2 ht2 htW hcard
  set T : Subgroup G := ((L₁.subgroupOf (normalizer (W : Set G))).map ν ⊔
    zpowers (ν ⟨t, htW⟩)).comap ν |>.map (normalizer (W : Set G)).subtype with hT
  have hVT : V ≤ T := by
    intro v hv
    have hv' : v ∈ W ⊓ centralizer ({t} : Set G) := by rw [hWt]; exact hv
    have hvW : v ∈ W := (Subgroup.mem_inf.1 hv').1
    have hvN : v ∈ normalizer (W : Set G) := le_normalizer hvW
    refine ⟨⟨v, hvN⟩, Subgroup.mem_comap.2 ?_, rfl⟩
    have h1 : ν ⟨v, hvN⟩ = 1 := (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 hvW)
    rw [h1]
    exact one_mem _
  have hLT : L₁ ≤ T := by
    intro l hl
    exact ⟨⟨l, hLW hl⟩, Subgroup.mem_comap.2
      (mem_sup_left ⟨⟨l, hLW hl⟩, mem_subgroupOf.2 hl, rfl⟩), rfl⟩
  have htT : t ∈ T :=
    ⟨⟨t, htW⟩, Subgroup.mem_comap.2 (mem_sup_right (mem_zpowers _)), rfl⟩
  have hsupT : V ⊔ L₁ ⊔ zpowers t ≤ T := sup_le (sup_le hVT hLT) ((zpowers_le).2 htT)
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
  have hcomm : ν g * ν ⟨t, htW⟩ = ν ⟨t, htW⟩ * ν g := mem_centralizer_singleton_iff.1 hx
  have hw : (g : G) * t * (g : G)⁻¹ * t⁻¹ ∈ W := by
    have h1 : ν (g * ⟨t, htW⟩ * g⁻¹ * (⟨t, htW⟩ : normalizer (W : Set G))⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    rw [hν, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
    simpa using h1
  set w := (g : G) * t * (g : G)⁻¹ * t⁻¹ with hwdef
  have hwt' : w * t = (g : G) * t * (g : G)⁻¹ := by rw [hwdef]; group
  have hwt : w * t * (w * t) = 1 := by
    rw [hwt']
    calc (g : G) * t * (g : G)⁻¹ * ((g : G) * t * (g : G)⁻¹) = (g : G) * (t * t) * (g : G)⁻¹ := by
          group
      _ = 1 := by rw [ht2]; group
  obtain ⟨u, huW, hu⟩ := exists_conj_eq_of_mul_self_eq_one hW2 ht2 hsurj hw hwt
  have hugt : u⁻¹ * (g : G) ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h1 : (g : G) * t * (g : G)⁻¹ = u * t * u⁻¹ := by rw [← hwt', hu]
    calc u⁻¹ * g * t = u⁻¹ * ((g : G) * t * (g : G)⁻¹) * g := by group
      _ = u⁻¹ * (u * t * u⁻¹) * g := by rw [h1]
      _ = t * (u⁻¹ * g) := by group
  have huN : u ∈ normalizer (W : Set G) := le_normalizer huW
  have hugN : u⁻¹ * (g : G) ∈ normalizer (W : Set G) := mul_mem (inv_mem huN) g.2
  have hugV : u⁻¹ * (g : G) ∈ normalizer (V : Set G) := by
    have h1 := mem_normalizer_inf_centralizer hugN (mem_centralizer_singleton_iff.1 hugt)
    rw [hWt] at h1
    exact h1
  obtain ⟨y, hy, hyeq⟩ := hsupT (hNV (Subgroup.mem_inf.2 ⟨hugV, hugt⟩))
  have hyval : y = (⟨u, huN⟩ : normalizer (W : Set G))⁻¹ * g := Subtype.ext (by simpa using hyeq)
  replace hy := Subgroup.mem_comap.1 hy
  rw [hyval, map_mul, map_inv] at hy
  have hνu : ν ⟨u, huN⟩ = 1 := (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 huW)
  rw [hνu, inv_one, one_mul] at hy
  exact hy

end Bar

theorem lSixNOneCentralizerInput : LSixNOneCentralizerInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hcc : c ∉ ({c}ᶜ : Finset (Fin 6)) := by simp
  have hcard : Nat.card W₁ = Nat.card (W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2 := by
    rw [hW₁c, hW₁t, natCard_modelToG_eq, pointRadical, card_pointRadOn hK c hcc,
      Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
    norm_num
  exact centralizer_mk_le_sup_of_normalizer_inf_le ht2 hW₁2 hcard hW₁t htN hLN
    (normalizer_pointRadical_inf_le hset (by norm_num) hK e ht hKt c)

theorem linearTwoSwapRowAtInput_six_of_notNormal
    (hcat : SLmCatalogueClausesAt 5) (hdet : SLmEvenTypeDetAt 5) (hC1 : LSixNOneNotNormalInput)
    (hlift : LSixFieldNOneLiftInput) (hswap : LSixSwapNOneInput) : LinearTwoSwapRowAtInput 6 :=
  linearTwoSwapRowAtInput_six_of_std hcat hdet lSixNOneCentralizerInput hC1 hlift hswap

end CFSG.SeitzReduction.LinearPilot
