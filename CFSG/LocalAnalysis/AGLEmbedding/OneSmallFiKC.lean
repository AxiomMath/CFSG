module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallFiKCEven
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallFiKCCz
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallFiKCAb
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallFiKCBOne
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallFiKCL34
import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D1SmallKCLeft : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → ∀ z : G, D1SmallCZElt p H R K z →
    ¬ D1CzSP p z → ¬ D1CzIso p z K → D1SmallOpenPosIf p M H Rbar K → D1SmallLa p M H Rbar K →
    ((p = 3 ∧ ¬ D1CzOutside p z) ∨
      (D1CzOutside p z ∧ D1CzB0 p R z ∧ D1CzEven p z ∧
        (∀ u ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G), ∀ r ∈ R,
          u * r * u⁻¹ * r⁻¹ ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) ∧
        ¬ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤
          Subgroup.centralizer (R : Set G))) → False

theorem d1SmallKC_of (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp)
    (hNo2 : KFactSmallNoTwo) (hShape : KFactSmallSylowShape) (hOrb : KFactSmallOrbits)
    (hFN : KFactFi22NoTwo) (hFO : KFactFi22Orbits) (hSch : KFactCatalogSchreier)
    (hRk : KFactSmallOfRankTwo) (hInvC : KFactSmallInvolveCard) (hCov : KFactCoverRankFive)
    (hGen : KFactL34OuterGen) (hAE : KFactL34AutExp) (hG6 : D1SmallL34)
    (hLeft : D1SmallKCLeft) : D1SmallKC := by
  intro G _ _ p P M H R Rbar K hd huniq z hz hnSP hnIso hOP
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  have : Fact p.Prime := ⟨hp⟩
  by_cases hLa : D1SmallLa p M H Rbar K
  swap
  · simp only [D1SmallLa, not_imp, not_and_or, not_not] at hLa
    obtain ⟨h3, hL34, hbc⟩ := hLa
    exact hG6 G p P M H R Rbar K hd huniq z hz h3 hL34 (hbc.imp id Or.inl)
  have hL := hLeft G p P M H R Rbar K hd huniq z hz hnSP hnIso hOP hLa
  obtain ⟨m, T, Pbar, KC, -, hRT, hTP, hc⟩ := hd.exists_czReduced hz
  by_cases hout : D1CzOutside p z
  swap
  · by_cases h3 : p = 3
    · exact hL (Or.inl ⟨h3, hout⟩)
    have h5 : 5 ≤ p := by
      have h2 := hp.two_le
      have h4 : p ≠ 4 := by rintro rfl; exact absurd hp (by decide)
      omega
    simp only [D1CzOutside, not_forall, not_not] at hout
    obtain ⟨KC', hKC', hzKC'⟩ := hout
    rw [hc.unique KC' hKC'] at hzKC'
    have hZne := center_ne_bot_of_mem hp hc.center hc.order hzKC'
    have hZp := isPGroup_center_of_isComponentOf hp hc.red.core_eq_bot hc.comp
    have h4 := hCov KC hc.comp.2.2 (hc.catalog.isCatalogGroup_center_quotient hc.comp) p hp h5
      hZne hZp
    obtain ⟨TK, hTK⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Pbar
      hc.normal.isSubnormal
    rw [← (SectionRank.pRank_sylow TK).1,
      ← pRank_map_of_injective p hp KC.subtype KC.subtype_injective, hTK] at h4
    have h3' := (pRank_mono p hp (inf_le_left : (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC ≤
      Pbar)).trans (hc.pRank_eq_three hnSP).le
    exact absurd (h4.trans h3') (by omega)
  have hzK : d1CzElt p z ∉ KC := hout KC hc.comp
  obtain ⟨hZKC, hsimple, hnonab, hcat, TC, hTC, hTCnc, hΓ, hAut, hcardTC⟩ :=
    hd.czComponent_facts_of_not_mem hSch hRk hInvC hz hc hnSP hzK
  have hcardKC : Nat.card ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC : Subgroup _) =
      Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K : Subgroup _) := by
    rw [← hTC, Subgroup.card_map_of_injective KC.subtype_injective, hcardTC]
  have hexp : ∀ t ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC, t ^ p = 1 := by
    intro t ht
    obtain ⟨n, hn⟩ := Pbar.isPGroup' ⟨t, ht.1⟩
    have htn : t ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hk1 : (⟨t, ht.2⟩ : KC) ^ p ^ n = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact htn)
    have h1 := hExp KC hsimple hnonab hcat p hp hp2 TC hTCnc hΓ hAut ⟨t, ht.2⟩ ⟨n, hk1⟩
    simpa using congrArg Subtype.val h1
  have hNoTwoKC : ∀ (S : Sylow p KC) (W : Subgroup KC), IsPGroup 2 W →
      (S : Subgroup KC) ≤ Subgroup.normalizer (W : Set KC) → W = ⊥ :=
    fun S W hW hSW => kFactSmallNoTwo_all hNo2 hFN KC hsimple hnonab hcat p hp hp2 TC hTCnc
      hΓ hAut S W hW hSW
  by_cases hB0 : D1CzB0 p R z
  · obtain ⟨hcardR, -⟩ := hd.card_le_and_decomp_of_b0 hOut hExp hz hB0 hLa
    by_cases hE : D1CzEven p z
    · exact hL (Or.inr ⟨hout, hB0, hE,
        hd.twoCore_comm_mem_core_of_reduced hz hB0 hRT hc hZKC hcardKC hNoTwoKC hcardR,
        hd.false_of_twoCore_le hOut hExp hShape hOrb hFO hz hB0 hLa⟩)
    exact hd.false_of_twoCore_le hOut hExp hShape hOrb hFO hz hB0 hLa
      (hd.twoCore_inf_centralizer_le_of_reduced hz hB0 hE hRT hc hZKC hcardKC hNoTwoKC hcardR)
  · by_cases hL34 : p = 3 ∧ IsLinThreeFour KC
    · by_cases hOPz : D1CzOuterP p z
      · exact hd.false_of_b1_l34_of_reduced hGen hAE hz hnSP hL34.1 hOPz hRT hTP hc hZKC hzK
          hL34.2 hexp hcardKC
      · refine hd.false_of_b1_of_reduced hz hnSP hB0 hRT hTP hc hZKC hzK (fun x hx => ?_) hexp
          hcardKC
        by_contra hxn
        exact hOPz ⟨KC, hc.comp, x, hx, hxn⟩
    · refine hd.false_of_b1_of_reduced hz hnSP hB0 hRT hTP hc hZKC hzK (fun x hx => ?_) hexp
        hcardKC
      have := hc.normal
      obtain ⟨n, hxn'⟩ := hx
      refine mem_sup_centralizer_of_congr (MulEquiv.refl KC)
        (hOut KC hsimple hnonab hcat p hp hp2 TC hTCnc hΓ hAut hL34 _ ⟨n, ?_⟩)
      rw [← map_pow, ← map_pow, hxn', map_one, map_one]

end CFSG.AGLEmbedding
