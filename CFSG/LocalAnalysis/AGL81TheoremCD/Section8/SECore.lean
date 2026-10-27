module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.Defs
import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.OddCore
import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer
import CFSG.RankThree.PartOne.CTP.StrongPQuotient
import CFSG.GroupTheory.PGroup.ElemAbelianSq
import CFSG.GroupTheory.ABGLocalTools.Constraint
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section8

open CFSG.Open
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive CoverActsTriviallyOnSmall)

variable {G : Type} [Group G] [Finite G]

theorem pRank_le_pRank_top_quotient_pPrimeCore {p : ℕ} (hp : p.Prime)
    {H K : Subgroup G} (hK : K ≤ H) :
    CFSG.Open.pRank p K ≤
      CFSG.Open.pRank p (⊤ : Subgroup (↥H ⧸ CFSG.pPrimeCore p ↥H)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmono : CFSG.Open.pRank p K ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥H) := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup H]
    exact CFSG.SectionRank.pRank_mono hp.one_lt hK
  rw [CFSG.SectionRank.pRank_quotient_eq (CFSG.pPrimeCore p ↥H)
    ((hp.coprime_iff_not_dvd).mp (CFSG.pPrimeCore_coprime_card (G := ↥H) (p := p)))]
  exact hmono

theorem isStronglyPEmbedded_map_quotient_pPrimeCore {p r : ℕ} {M H : Subgroup G}
    (hM : IsStronglyPEmbedded r M) (hr : r.Prime) (hHM : ¬ H ≤ M)
    (hdvd : r ∣ Nat.card (H ⊓ M : Subgroup G))
    (hKle : CFSG.pPrimeCore p ↥H ≤ (H ⊓ M).subgroupOf H) :
    IsStronglyPEmbedded r
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hY := hM.subgroupOf hHM hdvd
  exact hY.map_quotient hKle (hY.not_dvd_card_of_normal_le hKle)

theorem coverActsTriviallyOnSmall_of_stronglyEmbeddedFive
    (hSE : StronglyEmbeddedFive) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {M H : Subgroup G}
    (hM : IsStronglyPEmbedded p M) (hKH : CFSG.Open.IsKGroup ↥H)
    (hHM : ¬ H ≤ M) (hrank : 2 ≤ CFSG.Open.pRank p (H ⊓ M)) :
    CoverActsTriviallyOnSmall p
      ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore p ↥H)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hKQ : CFSG.Open.IsKGroup (↥H ⧸ CFSG.pPrimeCore p ↥H) :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_quotient' hKH _
  have hO : CFSG.pPrimeCore p (↥H ⧸ CFSG.pPrimeCore p ↥H) = ⊥ :=
    CFSG.pPrimeCore_quotient_eq_bot hp
  have hrank' : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥H ⧸ CFSG.pPrimeCore p ↥H)) :=
    hrank.trans (pRank_le_pRank_top_quotient_pPrimeCore hp (inf_le_left : H ⊓ M ≤ H))
  have hdvd : p ∣ Nat.card (H ⊓ M : Subgroup G) :=
    CFSG.GroupTheory.dvd_card_of_one_le_pRank hp (by omega)
  have hKle : CFSG.pPrimeCore p ↥H ≤ (H ⊓ M).subgroupOf H := fun x hx =>
    Subgroup.mem_subgroupOf.mpr ⟨x.2,
      CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.pPrimeCore_le hM hp hrank
        (Subgroup.mem_map_of_mem H.subtype hx)⟩
  have hN : IsStronglyPEmbedded p
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))) :=
    isStronglyPEmbedded_map_quotient_pPrimeCore hM hp hHM hdvd hKle
  exact (hSE p hp h5 _ hKQ hO hrank' _ hN).1

theorem pRank_le_three_of_normal_odd {M H K : Subgroup G}
    (hC : CStarGen G) (hM : CFSG.Open.rankThreeIsMaxTwoLocal M)
    (hs : ∀ r ∈ sigmaSet G M, IsStronglyPEmbedded r M)
    (hKH : K ≤ H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hKM : K ≤ M) (hHM : ¬ H ≤ M) (hKodd : Odd (Nat.card K))
    {r : ℕ} (hr : r.Prime) : CFSG.Open.pRank r K ≤ 3 := by
  by_cases hr2 : r = 2
  · subst hr2
    have hnot : ¬ 2 ∣ Nat.card K := fun h =>
      (Nat.not_even_iff_odd.mpr hKodd) (even_iff_two_dvd.mpr h)
    have h0 : CFSG.Open.pRank 2 K = 0 := by
      by_contra hne
      exact hnot (CFSG.GroupTheory.dvd_card_of_one_le_pRank Nat.prime_two (by omega))
    omega
  · by_cases hrσ : r ∈ sigmaSet G M
    · have hnot : ¬ r ∣ Nat.card K := by
        intro hdvd
        haveI : Fact r.Prime := ⟨hr⟩
        haveI : (K.subgroupOf H).Normal :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
        have hcard : Nat.card (K.subgroupOf H) = Nat.card K :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
        have hY := (hs r hrσ).subgroupOf hHM
          (hdvd.trans (Subgroup.card_dvd_of_le (le_inf hKH hKM)))
        refine hY.not_dvd_card_of_normal_le (S := K.subgroupOf H)
          (fun x hx => Subgroup.mem_subgroupOf.mpr
            ⟨x.2, hKM (Subgroup.mem_subgroupOf.mp hx)⟩) ?_
        rw [hcard]
        exact hdvd
      have h0 : CFSG.Open.pRank r K = 0 := by
        by_contra hne
        exact hnot (CFSG.GroupTheory.dvd_card_of_one_le_pRank hr (by omega))
      omega
    · exact (CFSG.SectionRank.pRank_mono hr.one_lt hKM).trans
        (hC.pRank_le_three_of_not_mem_sigmaSet hM hr hr2 hrσ)

namespace S8Core

theorem two_le_pRank_quotient_pPrimeCore (k : S8Core G) {H : Subgroup G} (hH : k.Config H) :
    2 ≤ CFSG.Open.pRank k.q (⊤ : Subgroup (↥H ⧸ CFSG.pPrimeCore k.q ↥H)) :=
  hH.two_le_pRank.trans
    (pRank_le_pRank_top_quotient_pPrimeCore k.prime (inf_le_left : H ⊓ k.M ≤ H))

theorem isStronglyPEmbedded_map_quotient_pPrimeCore (k : S8Core G) {H : Subgroup G}
    (hH : k.Config H) :
    IsStronglyPEmbedded k.q
      (((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.q ↥H))) := by
  have hdvd : k.q ∣ Nat.card (H ⊓ k.M : Subgroup G) :=
    CFSG.GroupTheory.dvd_card_of_one_le_pRank k.prime
      ((show 1 ≤ 2 by norm_num).trans hH.two_le_pRank)
  have hKle : CFSG.pPrimeCore k.q ↥H ≤ (H ⊓ k.M).subgroupOf H := fun x hx =>
    Subgroup.mem_subgroupOf.mpr ⟨x.2,
      k.pPrimeCore_le hH (Subgroup.mem_map_of_mem H.subtype hx)⟩
  exact CFSG.LocalAnalysis.AGL81TheoremCD.Section8.isStronglyPEmbedded_map_quotient_pPrimeCore
    k.strongQ k.prime hH.not_le hdvd hKle

theorem isSimpleGroup_generalizedFitting_quotient (k : S8Core G) {H : Subgroup G}
    (hH : k.Config H) :
    IsSimpleGroup ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.q ↥H)) ∧
      (∃ a b : ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.q ↥H)), a * b ≠ b * a) ∧
      (CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.q ↥H)).Normal ∧
      Subgroup.centralizer ((CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.q ↥H) :
        Subgroup (↥H ⧸ CFSG.pPrimeCore k.q ↥H)) :
        Set (↥H ⧸ CFSG.pPrimeCore k.q ↥H)) = ⊥ := by
  have hp : k.q.Prime := k.prime
  haveI : Fact k.q.Prime := ⟨hp⟩
  let K₀ : Subgroup ↥H := CFSG.pPrimeCore k.q ↥H
  let Lbar : Subgroup (↥H ⧸ K₀) := CFSG.generalizedFitting (↥H ⧸ K₀)
  have hO : CFSG.pPrimeCore k.q (↥H ⧸ K₀) = ⊥ := CFSG.pPrimeCore_quotient_eq_bot hp
  have hY : IsStronglyPEmbedded k.q
      (((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' K₀)) :=
    isStronglyPEmbedded_map_quotient_pPrimeCore k hH
  exact CFSG.RankThree.PartOne.Sec1511.spe_fstar hp hO hY

theorem coverActsTriviallyOnSmall_of_stronglyEmbeddedFive (k : S8Core G) (h5 : 5 ≤ k.q)
    {H : Subgroup G} (hH : k.Config H) (hSE : StronglyEmbeddedFive) :
    CoverActsTriviallyOnSmall k.q
      ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.q ↥H)) :=
  CFSG.LocalAnalysis.AGL81TheoremCD.Section8.coverActsTriviallyOnSmall_of_stronglyEmbeddedFive
    hSE k.prime h5 k.strongQ
    (CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper k.cstar.kProper hH.ne_top)
    hH.not_le hH.two_le_pRank

theorem pRank_pPrimeCore_le_three (k : S8Core G) {H : Subgroup G} (hH : k.Config H)
    {r : ℕ} (hr : r.Prime) :
    CFSG.Open.pRank r ((CFSG.pPrimeCore k.q ↥H).map H.subtype) ≤ 3 :=
  pRank_le_three_of_normal_odd k.cstar k.maxLocal k.strong
    (Subgroup.map_subtype_le (CFSG.pPrimeCore k.q ↥H))
    (CFSG.ABGLocalTools.le_normalizer_map_subtype H (CFSG.pPrimeCore k.q ↥H))
    (k.pPrimeCore_le hH) hH.not_le
    (by
      rw [Subgroup.card_map_of_injective H.subtype_injective]
      exact k.odd_card_pPrimeCore hH) hr

end S8Core

end CFSG.LocalAnalysis.AGL81TheoremCD.Section8
