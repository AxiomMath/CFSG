module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O1517bDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTen

import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.StarQuot
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15O1517bBase
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineEightB
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.LayerOfNotConstrained
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightFourProof
import CFSG.RankThree.PartOne.CTP.StrongPQuotient
import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer
import CFSG.GH74.Uniqueness.Section7Lemma711

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G]

private theorem pRank_three_eq_three_of_not_mem_sigmaSet (hC : CStarGen G) {M P : Subgroup G}
    (hM : rankThreeIsMaxTwoLocal M) (hPM : P ≤ M) (h3 : 3 ∉ sigmaSet G M)
    (hP3 : 3 ≤ CFSG.Open.pRank 3 P) : CFSG.Open.pRank 3 P = 3 := by
  refine le_antisymm ?_ hP3
  exact (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hPM).trans
    (hC.pRank_le_three_of_not_mem_sigmaSet hM Nat.prime_three (by norm_num) h3)

private theorem five_le_of_mem_sigmaM {M : Subgroup G} {p : ℕ}
    (hp : p ∈ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M) (hp3 : p ≠ 3) : 5 ≤ p := by
  have hpp : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  have hp2 : p ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p hp.1
  have hp4 : 4 ≤ p := by
    have := hpp.two_le
    omega
  have hp4ne : p ≠ 4 := by
    rintro rfl
    norm_num at hpp
  omega

private theorem normalizer_ne_top (hC : CStarGen G) {A : Subgroup G}
    (hA : Nat.card A = 3) : Subgroup.normalizer (A : Set G) ≠ ⊤ := by
  haveI : IsSimpleGroup G := hC.simple
  intro htop
  have hAn : A.Normal := (Subgroup.normalizer_eq_top_iff).mp htop
  have hAne : A ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hA
    omega
  have hAtop : A = ⊤ := (Subgroup.Normal.eq_bot_or_eq_top A).resolve_left hAne
  have hcardG : Nat.card G = 3 := by
    rw [← Subgroup.card_top (G := G), ← hAtop, hA]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic G := isCyclic_of_prime_card (p := 3) hcardG
  haveI : IsMulCommutative G := inferInstance
  obtain ⟨a, b, hab⟩ := hC.nonab
  exact hab (mul_comm a b)

private theorem relPPrimeCore_le_of_three_le_pRank {M R H P : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf 3 R M)
    (hΓ : rankThreeGamma 2 3 R ≤ M) (hPM : P ≤ M) (hPH : P ≤ H)
    (hP3 : 3 ≤ CFSG.Open.pRank 3 P) :
    CFSG.Open.relPPrimeCore 3 H ≤ M := by
  obtain ⟨E, hEP, hE, hcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3) (k := 3) hP3
  refine CFSG.LocalAnalysis.RankThreeUC.S15.O1517b.relPPrimeCore_le_of_two_le_pRank
    hR hΓ (hEP.trans hPM) (hEP.trans hPH) hE ?_
  rw [hcard]
  norm_num

private theorem strong_starImg {M H : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hMstrong : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M) (hHM : ¬ H ≤ M)
    (hpM : p ∣ Nat.card ↥(H ⊓ M)) (hKM : CFSG.Open.relPPrimeCore 3 H ≤ M) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded p
      (CFSG.LocalAnalysis.RankThreeUC.AGL81C.starImg 3 H M) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup ↥H := primeComplementCore (G := ↥H) 3
  let Y : Subgroup ↥H := (H ⊓ M).subgroupOf H
  have hNM : N.map H.subtype ≤ M := by
    rw [← CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.NineEightFour.relPPrimeCore_eq_map
      (p := 3) Nat.prime_three H]
    exact hKM
  have hNY : N ≤ Y := by
    change N ≤ (H ⊓ M).comap H.subtype
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_inf (Subgroup.map_subtype_le N) hNM
  have hpN : ¬ p ∣ Nat.card N := by
    intro hpdvd
    have hdvd : p ∣ Nat.card ↥(CFSG.Open.relPPrimeCore 3 H) := by
      rw [CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.NineEightFour.relPPrimeCore_eq_map
        (p := 3) Nat.prime_three H, Subgroup.card_map_of_injective H.subtype_injective]
      exact hpdvd
    have hNH : CFSG.Open.relPPrimeCore 3 H ≤ H := by
      rw [CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.NineEightFour.relPPrimeCore_eq_map
        (p := 3) Nat.prime_three H]
      exact Subgroup.map_subtype_le N
    exact hHM (CFSG.LocalAnalysis.RankThreeUC.S15.O1517b.le_of_normal_of_dvd_of_strong hp
      (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
        Nat.prime_three H) hNH hKM hdvd hMstrong)
  have hsub : CFSG.RankThree.PartOne.IsStronglyPEmbedded p Y := hMstrong.subgroupOf hHM hpM
  have hmap := hsub.map_quotient (N := N) hNY hpN
  simpa [CFSG.LocalAnalysis.RankThreeUC.AGL81C.starImg, Y, N,
    Subgroup.inf_subgroupOf_right, inf_comm] using hmap

private theorem shape_starImg {H P : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup 3 P)
    (hPs : (CFSG.Open.IsElemAbelian 3 P ∧ Nat.card P = 27) ∨
      IsCyclic ↥(Subgroup.center ↥P)) :
    (CFSG.Open.IsElemAbelian 3 (AGL81C.starImg 3 H P) ∧
        Nat.card ↥(AGL81C.starImg 3 H P) = 27) ∨
        IsCyclic ↥(Subgroup.center ↥(AGL81C.starImg 3 H P)) := by
  rcases hPs with ⟨hE, hc⟩ | hcyc
  · refine Or.inl ⟨(isElemAbelian_starImg_iff (H := H) (p := 3) Nat.prime_three
      hPH hP).mpr hE, ?_⟩
    rw [← Nat.card_congr (starImgMulEquiv (H := H) (p := 3) Nat.prime_three hPH hP).toEquiv]
    exact hc
  · exact Or.inr ((isCyclic_center_starImg_iff (H := H) (p := 3) Nat.prime_three
      hPH hP).mpr hcyc)

private theorem card_starImg {H A : Subgroup G} (hAH : A ≤ H) (hA3 : IsPGroup 3 A)
    (hA : Nat.card A = 3) : Nat.card ↥(AGL81C.starImg 3 H A) = 3 := by
  rw [← Nat.card_congr (starImgMulEquiv (H := H) (p := 3) Nat.prime_three hAH hA3).toEquiv]
  exact hA

private theorem red_of_not_mem_sigma {M H P A R : Subgroup G} {p : ℕ} (hC : CStarGen G)
    (hstrong : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M)
    (hp : p ∈ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M) (hp3 : p ≠ 3)
    (hAnH : (A.subgroupOf H).Normal) (hHne : H ≠ ⊤) (hHM : ¬ H ≤ M)
    (hcon : ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥H)
    (hR : CFSG.ABGLocalTools.IsSylowOf 3 R M)
    (hΓ : CFSG.Open.rankThreeGamma 2 3 R ≤ M)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (M ⊓ H))
    (hP3syl : CFSG.ABGLocalTools.IsSylowOf 3 P H)
    (hPrank : CFSG.Open.pRank 3 P = 3)
    (hPs : ((CFSG.Open.IsElemAbelian 3 P ∧ Nat.card P = 27) ∨
      IsCyclic ↥(Subgroup.center ↥P)) ∧ 3 ≤ CFSG.Open.pRank 3 P)
    (hKM : CFSG.Open.relPPrimeCore 3 H ≤ M) (hpM : p ∣ Nat.card ↥(H ⊓ M))
    (hPA : A ≤ P)
    (hshape : (CFSG.Open.IsElemAbelian 3 (AGL81C.starImg 3 H P) ∧
        Nat.card ↥(AGL81C.starImg 3 H P) = 27) ∨
        IsCyclic ↥(Subgroup.center ↥(AGL81C.starImg 3 H P)))
    (hcardA : Nat.card ↥(AGL81C.starImg 3 H A) = 3) :
    O1517bRed (AGL81C.StarGroup 3 H) p (AGL81C.starImg 3 H P) (AGL81C.starImg 3 H A)
      (AGL81C.starImg 3 H M) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpp : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  have hPM : P ≤ M := hP.le.trans inf_le_left
  have hPH : P ≤ H := hP.le.trans inf_le_right
  refine {
    prime := hpp
    five_le := five_le_of_mem_sigmaM hp hp3
    catalog := catalogSimpleSections_starGroup (p := 3)
      (CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hC.kProper H hHne)
    core := pPrimeCore_starGroup (H := H) (p := 3) Nat.prime_three
    layer_ne := by
      simpa only [AGL81C.StarGroup] using
        CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.layer_ne_bot_of_not_isPConstrained
          (X := ↥H) hcon
    sylow := isSylowOf_starImg_top (H := H) (p := 3) Nat.prime_three hP3syl
    rank := by
      rw [pRank_starImg_eq_pRank_inf (H := H) Nat.prime_three P, inf_eq_right.mpr hPH]
      exact hPrank
    shape := hshape
    card_A := hcardA
    normal_A := starImg_normal (H := H) (p := 3) (A := A) hAnH
    le_P := AGL81C.starImg_mono (p := 3) (H := H) hPA
    strong := strong_starImg (M := M) (H := H) (p := p) hpp hstrong hHM hpM hKM
    le_Y := AGL81C.starImg_mono (p := 3) (H := H) hPM
    gamma := rankThreeGamma_starImg_le (H := H) (p := 3) Nat.prime_three (k := 2)
      (B := P) (M := M) hPH hP.isPGroup (by
        intro D hDP hD2
        exact inf_le_left.trans
          (CFSG.LocalAnalysis.RankThreeUC.S15.O1517b.normalizer_le_of_two_le_pRank
            hR hΓ (hDP.trans hPM) (hP.isPGroup.to_le hDP) hD2)) }

theorem o1517b_le_or_red {G : Type} [Group G] [Finite G] (hC : CStarGen G) {M : Subgroup G}
    (hM : CFSG.Open.rankThreeIsMaxTwoLocal M)
    (hstrong : ∀ q ∈ sigmaSet G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded q M)
    {p : ℕ} (hp : p ∈ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M) {R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf 3 R M) (hΓ : CFSG.Open.rankThreeGamma 2 3 R ≤ M)
    {A : Subgroup G} (hAM : A ≤ M) (hA : Nat.card A = 3)
    (hpA : p ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (A : Set G))) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (M ⊓ Subgroup.normalizer (A : Set G)))
    (hPs : ((CFSG.Open.IsElemAbelian 3 P ∧ Nat.card P = 27) ∨ IsCyclic ↥(Subgroup.center ↥P))
      ∧ 3 ≤ CFSG.Open.pRank 3 P) :
    Subgroup.normalizer (A : Set G) ≤ M ∨
      O1517bRed (AGL81C.StarGroup 3 (Subgroup.normalizer (A : Set G))) p
        (AGL81C.starImg 3 (Subgroup.normalizer (A : Set G)) P)
        (AGL81C.starImg 3 (Subgroup.normalizer (A : Set G)) A)
        (AGL81C.starImg 3 (Subgroup.normalizer (A : Set G)) M) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let H : Subgroup G := Subgroup.normalizer (A : Set G)
  have hAH : A ≤ H := by simpa [H] using Subgroup.le_normalizer (H := A)
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by rw [hA]; norm_num)
  have hAne : A ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hA
    omega
  have hPM : P ≤ M := hP.le.trans inf_le_left
  have hPH : P ≤ H := hP.le.trans inf_le_right
  have hP3syl : CFSG.ABGLocalTools.IsSylowOf 3 P H :=
    CFSG.LocalAnalysis.RankThreeUC.S15.O1517b.isSylowOf_of_isSylowOf_inf hR hΓ hP (by omega)
  by_cases h3 : 3 ∈ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M
  · exact Or.inl ((hstrong 3 h3).normalizer_le hAne hA3 hAM)
  · have hp3 : p ≠ 3 := by
      intro hp3
      exact h3 (hp3 ▸ hp)
    have h3' : 3 ∉ sigmaSet G M := h3
    have hPrank : CFSG.Open.pRank 3 P = 3 :=
      pRank_three_eq_three_of_not_mem_sigmaSet hC hM hPM h3' hPs.2
    have hKM : CFSG.Open.relPPrimeCore 3 H ≤ M :=
      relPPrimeCore_le_of_three_le_pRank hR hΓ hPM hPH hPs.2
    have hHne : H ≠ ⊤ := normalizer_ne_top hC hA
    by_cases hHM : H ≤ M
    · exact Or.inl hHM
    · have hcon : ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥H := by
        intro hconH
        exact hHM (CFSG.LocalAnalysis.RankThreeUC.S15.O1517b.le_of_isPConstrained_of_three_le_pRank
          hR hΓ hP3syl hPM hPs.2 hconH hKM)
      have hpM : p ∣ Nat.card ↥(H ⊓ M) := by
        have hle : M ⊓ Subgroup.centralizer (A : Set G) ≤ H ⊓ M :=
          le_inf (inf_le_right.trans (Subgroup.centralizer_le_normalizer (A : Set G))) inf_le_left
        exact hpA.trans (Subgroup.card_dvd_of_le hle)
      have hPA : A ≤ P := by
        haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        exact CFSG.GH74.Uniqueness.le_of_isSylowOf_of_isPGroup_normal hP (le_inf hAM hAH)
          inf_le_right hA3
      have hshape := shape_starImg hPH hP.isPGroup hPs.1
      have hcardA := card_starImg hAH hA3 hA
      exact Or.inr (red_of_not_mem_sigma hC (hstrong p hp) hp hp3
        (by simpa [H] using Subgroup.normal_in_normalizer (H := A)) hHne hHM hcon hR hΓ hP
        hP3syl hPrank hPs hKM hpM hPA hshape hcardA)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
