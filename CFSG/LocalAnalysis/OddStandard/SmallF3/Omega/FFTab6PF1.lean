module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFFundamental

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private theorem ff_sq_of_orderOf_eq_two {G : Type} [Group G] {x : G} (hx : orderOf x = 2) :
    x * x = 1 := by
  rw [← pow_two, ← hx]
  exact pow_orderOf_eq_one x

private theorem ff_dinv_of_kindP {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : G}
    (hGA : CFSG.Open.GriessAllModelsStatement) (hL : IsOm6P L) (hs2 : orderOf s = 2)
    (hsn : s ∈ Subgroup.normalizer (L : Set G)) {k : ℕ} (h : KindP L s k) (hk : k < 5) :
    DInv L s k :=
  (ff_kindP_iff_dinv (k := k) hGA hL hs2 hsn hk).mp h

private theorem ff_kindP_of_dinv {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : G}
    (hGA : CFSG.Open.GriessAllModelsStatement) (hL : IsOm6P L) (hs2 : orderOf s = 2)
    (hsn : s ∈ Subgroup.normalizer (L : Set G)) {k : ℕ} (h : DInv L s k) (hk : k < 5) :
    KindP L s k :=
  (ff_kindP_iff_dinv (k := k) hGA hL hs2 hsn hk).mpr h

theorem ff_layer_trivial (hGA : CFSG.Open.GriessAllModelsStatement) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      (layerCent L s = ⊥ ↔
        InducesTypeSome L s 6 1 4 1 ∨ ∃ α : ℤˣ, InducesTypeSome L s 6 1 3 α) := by
  intro G _ _ L hL s hs2 hsn
  constructor
  · intro hl
    rcases ff_dinv_classify hGA hL hs2 hsn with hc | h0 | h1 | h2 | h3 | h4
    · have hz := ff_center_eq_bot_six_plus hGA hL
      have hev := ff_two_dvd_card_of_isOmega6Plus hL.2
      obtain ⟨hLay, -⟩ := ff_layerCent_eq_of_central hL.1 hz hev hc
      rw [hLay] at hl
      exact absurd hl (ff_isOmega6Plus_ne_bot hL.2)
    · exact Or.inl (ff_kindP_of_dinv hGA hL hs2 hsn h0 (by norm_num))
    · exact absurd hl (ff_isL29_ne_bot h1.2.2.1)
    · exact absurd hl (ff_isOmega5_ne_bot h2.2.1)
    · exact Or.inr (ff_kindP_of_dinv hGA hL hs2 hsn h3 (by norm_num))
    · rcases h4.2.1 with hL3 | hL2
      · exact absurd hl (ff_isL3Eps3_ne_bot hL3)
      · exact absurd hl (ff_isL29_ne_bot hL2)
  · rintro (h | h)
    · have h0 := ff_dinv_of_kindP hGA hL hs2 hsn (show KindP L s 0 from h) (by norm_num)
      exact ff_layerCent_eq_bot_of_solvable L s h0.2.2
    · have h3 := ff_dinv_of_kindP hGA hL hs2 hsn (show KindP L s 3 from h) (by norm_num)
      exact ff_layerCent_eq_bot_of_solvable L s h3.2

theorem ff_layer_i1 (hGA : CFSG.Open.GriessAllModelsStatement) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      (∃ α : ℤˣ, InducesTypeSome L s 6 1 1 α) → IsOmega5 (layerCent L s) := by
  intro G _ _ L hL s hs2 hsn h
  exact (ff_dinv_of_kindP hGA hL hs2 hsn (show KindP L s 2 from h) (by norm_num)).2.1

theorem ff_layer_i2 (hGA : CFSG.Open.GriessAllModelsStatement) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      InducesTypeSome L s 6 1 2 (-1) → IsL29 (layerCent L s) := by
  intro G _ _ L hL s hs2 hsn h
  exact (ff_dinv_of_kindP hGA hL hs2 hsn (show KindP L s 1 from h) (by norm_num)).2.2.1

theorem ff_layer_outer (hGA : CFSG.Open.GriessAllModelsStatement) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      InducesOutsideGStar L 6 1 s → IsL3Eps3 (layerCent L s) ∨ IsL29 (layerCent L s) := by
  intro G _ _ L hL s hs2 hsn h
  exact (ff_dinv_of_kindP hGA hL hs2 hsn (show KindP L s 4 from h) (by norm_num)).2.1

theorem ff_inner_iff (hGA : CFSG.Open.GriessAllModelsStatement) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      ((InnerOn L s ∧ s ∉ centralizer (L : Set G)) ↔
        InducesTypeSome L s 6 1 4 1 ∨ InducesTypeSome L s 6 1 2 (-1)) := by
  intro G _ _ L hL s hs2 hsn
  constructor
  · rintro ⟨hInner, hNotC⟩
    rcases ff_dinv_classify hGA hL hs2 hsn with hc | h0 | h1 | h2 | h3 | h4
    · exact absurd hc hNotC
    · exact Or.inl (ff_kindP_of_dinv hGA hL hs2 hsn h0 (by norm_num))
    · exact Or.inr (ff_kindP_of_dinv hGA hL hs2 hsn h1 (by norm_num))
    · exact absurd hInner h2.1
    · exact absurd hInner h3.1
    · exact absurd hInner h4.1
  · rintro (h | h)
    · have h0 := ff_dinv_of_kindP hGA hL hs2 hsn (show KindP L s 0 from h) (by norm_num)
      exact ⟨h0.1, h0.2.1⟩
    · have h1 := ff_dinv_of_kindP hGA hL hs2 hsn (show KindP L s 1 from h) (by norm_num)
      exact ⟨h1.1, h1.2.1⟩

theorem ff_i4_one_class (hGA : CFSG.Open.GriessAllModelsStatement) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ u u' : G, u ∈ L → u' ∈ L → orderOf u = 2 → orderOf u' = 2 →
      InducesTypeSome L u 6 1 4 1 → InducesTypeSome L u' 6 1 4 1 → u' ∈ conjClassIn L u := by
  intro G _ _ L hL u u' hu hu' hu2 hu2' hTu hTu'
  have hz := ff_center_eq_bot_six_plus hGA hL
  obtain ⟨V, _, _, _, Q, hQ, e, hdim, hsgn⟩ := ff_exists_model_six_plus hL
  have hun : u ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hu
  have hun' : u' ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hu'
  have hDu := ff_dinv_of_kindP hGA hL hu2 hun (show KindP L u 0 from hTu) (by norm_num)
  have hDu' := ff_dinv_of_kindP hGA hL hu2' hun' (show KindP L u' 0 from hTu') (by norm_num)
  have hKMu := ff_KM0_of_dinv0 hQ hdim hsgn hz e (ff_induces_of_mem hQ hz e hu)
    (ff_sq_of_orderOf_eq_two hu2) hDu
  have hKMu' := ff_KM0_of_dinv0 hQ hdim hsgn hz e (ff_induces_of_mem hQ hz e hu')
    (ff_sq_of_orderOf_eq_two hu2') hDu'
  exact (ff_mem_conjClass_iff hQ hz e hu hu').mpr (ff_conj_KM0 hQ hdim hKMu hKMu')

theorem ff_i2_one_class (hGA : CFSG.Open.GriessAllModelsStatement) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ u u' : G, u ∈ L → u' ∈ L → orderOf u = 2 → orderOf u' = 2 →
      InducesTypeSome L u 6 1 2 (-1) → InducesTypeSome L u' 6 1 2 (-1) → u' ∈ conjClassIn L u := by
  intro G _ _ L hL u u' hu hu' hu2 hu2' hTu hTu'
  have hz := ff_center_eq_bot_six_plus hGA hL
  obtain ⟨V, _, _, _, Q, hQ, e, hdim, hsgn⟩ := ff_exists_model_six_plus hL
  have hun : u ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hu
  have hun' : u' ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hu'
  have hDu := ff_dinv_of_kindP hGA hL hu2 hun (show KindP L u 1 from hTu) (by norm_num)
  have hDu' := ff_dinv_of_kindP hGA hL hu2' hun' (show KindP L u' 1 from hTu') (by norm_num)
  have hKMu := ff_KM1_of_dinv1 hQ hdim hsgn hz e (ff_induces_of_mem hQ hz e hu)
    (ff_sq_of_orderOf_eq_two hu2) hDu
  have hKMu' := ff_KM1_of_dinv1 hQ hdim hsgn hz e (ff_induces_of_mem hQ hz e hu')
    (ff_sq_of_orderOf_eq_two hu2') hDu'
  exact (ff_mem_conjClass_iff hQ hz e hu hu').mpr (ff_conj_KM1 hQ hdim hKMu hKMu')

end CFSG.OddStandard.SmallF3.Omega
