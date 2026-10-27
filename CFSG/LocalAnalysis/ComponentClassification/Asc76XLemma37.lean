module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76XPullback
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XBenderSub

public section

namespace CFSG.ComponentClassification.Asc76.Sec3Setting

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76X
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem perp_subset (Ω : Set (Subgroup G)) (K : Subgroup G) : perp Ω K ⊆ Ω := fun _ h => h.1

theorem mem_perp_self (hΩ : Sec3Setting Ω) {K : Subgroup G} (hK : K ∈ Ω) : K ∈ perp Ω K := by
  refine ⟨hK, ?_⟩
  rw [inf_of_le_left le_normalizer]
  exact (hΩ.tightlyEmbedded hK).1

theorem mem_perp_of_le_normalizer (hΩ : Sec3Setting Ω) {K J : Subgroup G} (hJ : J ∈ Ω)
    (h : J ≤ normalizer (K : Set G)) : J ∈ perp Ω K := by
  refine ⟨hJ, ?_⟩
  rw [inf_of_le_left h]
  exact (hΩ.tightlyEmbedded hJ).1

theorem le_normalizer_of_mem_perp (hΩ : Sec3Setting Ω) (h22 : Lemma22Four) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ perp Ω K) : J ≤ normalizer (K : Set G) := by
  by_cases hJK : J = K
  · rw [hJK]
    exact le_normalizer
  · exact (hΩ.lemma35 h22 hK hJ.1 hJK hJ.2).1

theorem sSup_perp_le_normalizer (hΩ : Sec3Setting Ω) (h22 : Lemma22Four) {K : Subgroup G}
    (hK : K ∈ Ω) : sSup (perp Ω K) ≤ normalizer (K : Set G) :=
  sSup_le fun _ hJ => hΩ.le_normalizer_of_mem_perp h22 hK hJ

theorem perp_conj_mem (hΩ : Sec3Setting Ω) {K J : Subgroup G} (hJ : J ∈ perp Ω K) {g : G}
    (hg : g ∈ normalizer (K : Set G)) : rightConjugate J g ∈ perp Ω K := by
  refine ⟨hΩ.conj_mem J hJ.1 g, ?_⟩
  have h : rightConjugate J g ⊓ normalizer (K : Set G) =
      rightConjugate (J ⊓ normalizer (K : Set G)) g := by
    ext x
    simp only [mem_inf, mem_rightConjugate_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, mul_mem (mul_mem hg h2) (inv_mem hg)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [this]
      exact mul_mem (mul_mem (inv_mem hg) h2) hg
  rw [h, rightConjugate_card]
  exact hJ.2

end CFSG.ComponentClassification.Asc76.Sec3Setting

namespace CFSG.ComponentClassification.Asc76X.MinCounter

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem card_sSup_perp_lt (hM : MinCounter Ω) (h22 : Lemma22Four) {K : Subgroup G}
    (hK : K ∈ Ω) : Nat.card ↥(sSup (perp Ω K)) < Nat.card G := by
  have hle := hM.setting.sSup_perp_le_normalizer h22 hK
  have hne : normalizer (K : Set G) ≠ ⊤ := fun h =>
    hM.lemma36 h22 hK (normalizer_eq_top_iff.mp h)
  have h1 : Nat.card (normalizer (K : Set G)) < Nat.card G :=
    lt_of_le_of_ne (card_le_card_group _) fun h => hne ((card_eq_iff_eq_top _).mp h)
  exact (card_le_of_le hle).trans_lt h1

theorem lemma37_one (hM : MinCounter Ω) (h22 : Lemma22Four) {K : Subgroup G} (hK : K ∈ Ω) :
    Conc4 (bar (sSup (perp Ω K)) '' perp Ω K) :=
  hM.conc4_bar (Sec3Setting.perp_subset Ω K)
    (fun _ hJ _ hx => hM.setting.perp_conj_mem hJ (hM.setting.sSup_perp_le_normalizer h22 hK hx))
    (Or.inr (hM.card_sSup_perp_lt h22 hK))

theorem lemma37_two (hM : MinCounter Ω) (h22 : Lemma22Four) (hB : BenderFacts)
    {K J L : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ perp Ω K) (hL : L ∈ perp Ω K) (hJL : J ≠ L) :
    J ∈ perp Ω L ∨ ∃ x ∈ J ⊔ L, L = rightConjugate J x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.setting
  set X := sSup (perp Ω K) with hXdef
  have hJX : J ≤ X := le_sSup hJ
  have hLX : L ≤ X := le_sSup hL
  obtain ⟨hC1, hC2⟩ := hM.lemma37_one h22 hK (bar X J) ⟨J, hJ, rfl⟩
  by_cases hconj : ∃ q, bar X L = rightConjugate (bar X J) q
  · right
    obtain ⟨q, hq⟩ := hconj
    rcases hC2 with hn | ⟨hsz, hsyl⟩
    · exfalso
      have h1 : bar X L = bar X J := by
        rw [hq]
        exact (rightConjugate_eq_self_iff _ _).mpr
          (by rw [normalizer_eq_top_iff.mpr hn]; exact mem_top q)
      exact hJL (hΩ.eq_of_bar_eq hJ.1 hL.1 hJX hLX h1.symm)
    · obtain ⟨RJ, hRJ⟩ := Sec3Setting.exists_sylow J
      obtain ⟨RL, hRL⟩ := Sec3Setting.exists_sylow L
      have hRJ' := isSylowOf_iff_card.mp hRJ
      have hRL' := isSylowOf_iff_card.mp hRL
      have hRJ2 : IsPGroup 2 RJ := IsPGroup.of_card hRJ'.2
      have hRL2 : IsPGroup 2 RL := IsPGroup.of_card hRL'.2
      have hPJ := hsyl _ (isSylowOf_bar hJX hRJ)
      have hLM : bar X L ≤ normalClosure ((bar X J : Subgroup (BarGroup X)) :
          Set (BarGroup X)) := by
        rw [hq]
        rintro _ ⟨y, hy, rfl⟩
        exact normalClosure_normal.conj_mem y (subset_normalClosure hy) _
      have hPL : IsSylowOf 2 (bar X RL) (normalClosure ((bar X J : Subgroup (BarGroup X)) :
          Set (BarGroup X))) := by
        rw [isSylowOf_iff_card] at hPJ ⊢
        refine ⟨(bar_mono hRL'.1).trans hLM, ?_⟩
        rw [← hPJ.2, card_bar_of_pGroup (hRL'.1.trans hLX) hRL2,
          card_bar_of_pGroup (hRJ'.1.trans hJX) hRJ2, hRL'.2, hRJ'.2,
          (hΩ.twoPart J hJ.1 L hL.1 hJL).1]
      have hne : bar X RJ ≠ bar X RL := by
        intro h
        apply hJL
        refine hΩ.eq_of_pGroup_le hJ.1 hL.1 hRJ2 (hΩ.sylow_ne_bot hJ.1 hRJ) hRJ'.1 ?_
        intro r hr
        obtain ⟨k, hk⟩ := hRJ2 ⟨r, hr⟩
        have hk' : r ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
        have hrX : r ∈ X := hJX (hRJ'.1 hr)
        have h1 : barMk X ⟨r, hrX⟩ ∈ bar X L := bar_mono hRL'.1 (h ▸ ⟨⟨r, hrX⟩, hr, rfl⟩)
        exact hΩ.mem_of_barMk_mem hL.1 hLX (x := ⟨r, hrX⟩) hk' h1
      obtain ⟨m, hm, hmeq⟩ := hB.exists_conj_of_isSylowOf hsz hPJ hPL hne
      have hsup : bar X RJ ⊔ bar X RL = bar X (RJ ⊔ RL) := by
        rw [bar, bar, bar, subgroupOf_sup (hRJ'.1.trans hJX) (hRL'.1.trans hLX), Subgroup.map_sup]
      rw [hsup] at hm
      obtain ⟨x, hx, rfl⟩ := hm
      have hxJL : (x : G) ∈ J ⊔ L := (sup_le_sup hRJ'.1 hRL'.1) hx
      refine ⟨x, hxJL, ?_⟩
      rw [← bar_rightConjugate] at hmeq
      have hRJx2 : IsPGroup 2 (rightConjugate RJ x) := by
        rw [rightConjugate]
        exact hRJ2.map _
      have hRJxX : rightConjugate RJ x ≤ X := fun y hy => by
        rw [mem_rightConjugate_iff] at hy
        have h2 : (x : G) * y * (x : G)⁻¹ ∈ X := hJX (hRJ'.1 hy)
        have : y = (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * x := by group
        rw [this]
        exact mul_mem (mul_mem (inv_mem x.2) h2) x.2
      have hRJxL : rightConjugate RJ x ≤ L := by
        intro y hy
        obtain ⟨k, hk⟩ := hRJx2 ⟨y, hy⟩
        have hk' : y ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
        have h1 : barMk X ⟨y, hRJxX hy⟩ ∈ bar X L :=
          bar_mono hRL'.1 (hmeq ▸ ⟨⟨y, hRJxX hy⟩, hy, rfl⟩)
        exact hΩ.mem_of_barMk_mem hL.1 hLX (x := ⟨y, hRJxX hy⟩) hk' h1
      have hRJx1 : rightConjugate RJ x ≠ ⊥ := by
        intro h
        apply hΩ.sylow_ne_bot hJ.1 hRJ
        rw [eq_bot_iff]
        intro r hr
        have : (x : G)⁻¹ * r * x ∈ rightConjugate RJ x := by
          rw [mem_rightConjugate_iff]
          simpa [mul_assoc] using hr
        rw [h, mem_bot] at this
        rw [mem_bot]
        calc r = (x : G) * ((x : G)⁻¹ * r * x) * (x : G)⁻¹ := by group
          _ = 1 := by rw [this]; group
      refine hΩ.eq_of_pGroup_le hL.1 (hΩ.conj_mem J hJ.1 x) hRJx2 hRJx1 hRJxL ?_
      intro y hy
      rw [mem_rightConjugate_iff] at hy ⊢
      exact hRJ'.1 hy
  · left
    push Not at hconj
    have hc := hC1 (bar X L) ⟨L, hL, rfl⟩ fun q hq => hconj q hq
    refine hΩ.mem_perp_of_le_normalizer hJ.1 fun j hj => ?_
    have hjX : j ∈ X := hJX hj
    have hjC : barMk X ⟨j, hjX⟩ ∈ centralizer ((bar X L : Subgroup (BarGroup X)) :
        Set (BarGroup X)) :=
      commutator_eq_bot_iff_le_centralizer.mp hc ⟨⟨j, hjX⟩, hj, rfl⟩
    exact hΩ.mem_normalizer_of_barMk hL.1 hLX (centralizer_le_normalizer _ hjC)

end CFSG.ComponentClassification.Asc76X.MinCounter
