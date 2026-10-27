module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFive
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.JSubNormalizer
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.Helpers
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.GroupTheory.SylowNormalIndex
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27DiagGroup
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFour

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

@[expose] def TenFifteenSigma (M H : Subgroup G) : Prop :=
  ∀ d : ℕ, d ∈ sigmaSet G M → ∃ D : Subgroup G, IsSylowOf d D M ∧ D ≤ (H ⊓ M) ⊔ jSub M H

theorem sylow_le_jSub_of_sylow_le_jSub {M H D₀ : Subgroup G} {d : ℕ} (hd : d.Prime)
    (hD₀ : IsSylowOf d D₀ M) (hD₀J : D₀ ≤ jSub M H) :
    ∀ D : Subgroup G, IsSylowOf d D M → D ≤ jSub M H := by
  classical
  have : Fact d.Prime := ⟨hd⟩
  have hD₀N : D₀ ≤ twoPrimeLayer M := hD₀J.trans (jSub_le_twoPrimeLayer M H)
  have hnot : ¬ d ∣ (twoPrimeLayer M).relIndex M := by
    intro hdvd
    have hrel : D₀.relIndex M =
        D₀.relIndex (twoPrimeLayer M) * (twoPrimeLayer M).relIndex M :=
      (Subgroup.relIndex_mul_relIndex D₀ (twoPrimeLayer M) M hD₀N
        (twoPrimeLayer_le M)).symm
    exact (isSylowOf_iff.mp hD₀).2.2 (hrel ▸ dvd_mul_of_dvd_right hdvd _)
  intro D hD
  have hDN : D ≤ twoPrimeLayer M :=
    le_of_isPGroup_of_not_dvd_relIndex hD.isPGroup hD.le (twoPrimeLayer_le M)
      (le_normalizer_twoPrimeLayer M) hnot
  have hD₀syl : IsSylowOf d D₀ (twoPrimeLayer M) :=
    hD₀.of_le hD₀N (twoPrimeLayer_le M)
  have hDsyl : IsSylowOf d D (twoPrimeLayer M) :=
    hD.of_le hDN (twoPrimeLayer_le M)
  obtain ⟨k, hkN, hconj⟩ := hDsyl.exists_mem_conj hD₀syl
  have hkJ : k ∈ Subgroup.normalizer (jSub M H : Set G) :=
    twoPrimeLayer_le_normalizer_jSub M H hkN
  intro x hxD
  have hy : k * x * k⁻¹ ∈ D₀ := (hconj (k * x * k⁻¹)).mpr (by
    have hx : k⁻¹ * (k * x * k⁻¹) * k = x := by group
    rw [hx]
    exact hxD)
  have hmem := (Subgroup.mem_normalizer_iff.mp (inv_mem hkJ) (k * x * k⁻¹)).mp
    (hD₀J hy)
  have hx : k⁻¹ * (k * x * k⁻¹) * (k⁻¹)⁻¹ = x := by group
  rwa [hx] at hmem

theorem sylow_le_jSub_of_tenFifteenSigma {M H : Subgroup G} {d : ℕ} (hdσ : d ∈ sigmaSet G M)
    (hdH : ¬ d ∣ Nat.card (H ⊓ M : Subgroup G)) (h1015 : TenFifteenSigma M H) :
    ∀ D : Subgroup G, IsSylowOf d D M → D ≤ jSub M H := by
  classical
  have hd : d.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hdσ.1
  have : Fact d.Prime := ⟨hd⟩
  obtain ⟨D₀, hD₀, hD₀le⟩ := h1015 d hdσ
  have hJH : H ⊓ M ≤ Subgroup.normalizer (jSub M H : Set G) := inf_le_normalizer_jSub M H
  have hMN : (H ⊓ M) ⊔ jSub M H ≤ Subgroup.normalizer (jSub M H : Set G) :=
    sup_le hJH Subgroup.le_normalizer
  have hidx : (jSub M H).relIndex ((H ⊓ M) ⊔ jSub M H) =
      (jSub M H).relIndex (H ⊓ M) :=
    CFSG.HardMathSupport.Lang.E6Descent.DiagGroup.relIndex_sup_right_of_le_normalizer
      (H ⊓ M) (jSub M H) hJH
  have hnot : ¬ d ∣ (jSub M H).relIndex ((H ⊓ M) ⊔ jSub M H) := by
    rw [hidx]
    exact fun h => hdH (h.trans (Subgroup.relIndex_dvd_card (jSub M H) (H ⊓ M)))
  have hD₀J : D₀ ≤ jSub M H :=
    le_of_isPGroup_of_not_dvd_relIndex hD₀.isPGroup hD₀le le_sup_right hMN hnot
  exact sylow_le_jSub_of_sylow_le_jSub hd hD₀ hD₀J

theorem hd3_of_tenFifteenSigma {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}
    (h : TwelveCtx G M p Q H) (h124 : TwelveFour M H) (h1015 : TenFifteenSigma M H) :
    ∀ d ∈ sigmaSet G M, 3 ≤ CFSG.Open.pRank d (jSub M H) := by
  intro d hdσ
  have hd : d.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hdσ.1
  have hdH : ¬ d ∣ Nat.card (H ⊓ M : Subgroup G) := (h124 d hdσ).1
  have hM3 : 3 ≤ CFSG.Open.pRank d M := h.cstar.three_le_pRank_of_mem_sigmaSet h.maxLocal hdσ
  have hle : CFSG.Open.pRank d M ≤ CFSG.Open.pRank d (jSub M H) := by
    obtain ⟨E, hEM, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hd.one_lt M
    have hEsub : IsPGroup d (E.subgroupOf M) :=
      CFSG.Open.IsElemAbelian.isPGroup hE |>.comap_subtype
    obtain ⟨P, hP⟩ := hEsub.exists_le_sylow
    have hD : IsSylowOf d ((P : Subgroup ↥M).map M.subtype) M := ⟨P, rfl⟩
    have hDle : (P : Subgroup ↥M).map M.subtype ≤ jSub M H :=
      sylow_le_jSub_of_tenFifteenSigma hdσ hdH h1015 _ hD
    have hEJ : E ≤ jSub M H := by
      intro x hx
      have hxsub : (⟨x, hEM hx⟩ : ↥M) ∈ E.subgroupOf M :=
        Subgroup.mem_subgroupOf.mpr hx
      exact hDle (Subgroup.mem_map_of_mem (f := M.subtype) (hP hxsub))
    exact CFSG.SectionRank.le_pRank hd.one_lt hEJ hE hcard
  omega

theorem twelveFive_of_twelveCtx_of_tenFifteen {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}
    (h : TwelveCtx G M p Q H) {d : ℕ} (hd : d.Prime) (hdσ : d ∈ sigmaSet G M)
    (h124 : TwelveFour M H) (h1015 : TenFifteenSigma M H)
    (hdvdL : ∀ L : Subgroup G, L ∈ weakBlockSet M H → d ∣ Nat.card L)
    (hr3 : (weakBlockSet M H).ncard ≤ CFSG.Open.pRank 3 (jSub M H))
    (hdr : CFSG.Open.pRank d (jSub M H) ≤ (weakBlockSet M H).ncard)
    (hL3 : ∀ L : Subgroup G, L ∈ weakBlockSet M H →
      ∃ n : ℕ, Odd n ∧ IsL3TwoPow n (↥L ⧸ pCore 2 ↥L)) :
    TwelveFive M H d := by
  have hd3 : 3 < d := (h124 d hdσ).2.1
  have hdH : ¬ d ∣ Nat.card (H ⊓ M : Subgroup G) := (h124 d hdσ).1
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · exact jSub_le_oPPrimeHull_of_blocks hd hd3 hdvdL hL3
  · exact oPPrimeHull_le_jSub_of_sylow
      (sylow_le_jSub_of_tenFifteenSigma hdσ hdH h1015)
  · exact twelveFive_part_two_of_rank_count
      (pRank_three_le_three_of_twelveCtx h h124) hr3 hdr
      (hd3_of_tenFifteenSigma h h124 h1015 d hdσ) hL3

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
