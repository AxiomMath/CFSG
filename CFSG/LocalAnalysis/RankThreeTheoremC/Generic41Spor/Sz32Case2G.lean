module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32SharedProp31
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32SharedFocal
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupSz32
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2GSeries
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2GData
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Pgroup
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Burnside
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankSetup
public import CFSG.LocalAnalysis.RankThreeTheoremC.FusionControl
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PSU3.Aut
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Decomp

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3K0 CentSeries)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem sz32_centSeries (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G) (hSz : Sz32Facts)
    (hSz' : Sz32OpenFacts) (hc : PointConfig IsSz32Type G 5 P M x J) {a c y : G}
    (hP : Sz32Struct P x J a c y) :
    ∃ N : Subgroup G, CentSeries 5 (M ⊓ Subgroup.centralizer ({x} : Set G)) (P : Subgroup G) N := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hpres := hP.pres_P
  have hPC := hP.le_cent
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  have hPW : (P : Subgroup G) ≤ M ⊓ Subgroup.centralizer ({x} : Set G) := le_inf hPM hPC
  have hcP : c ∈ (P : Subgroup G) := hpres.c_mem
  have hPK₀ : (P : Subgroup G) ⊓ u3K0 5 x J = Subgroup.zpowers c := by
    apply le_antisymm
    · intro q hq
      exact hP.decomp.QC q (by rw [u3S_eq_of_le_cent hPC]; exact hq.1) hq.2
    · exact le_inf (Subgroup.zpowers_le.mpr hcP) (Subgroup.zpowers_le.mpr hP.decomp.c_K0)
  have hDcyc : IsCyclic ↥((P : Subgroup G) ⊓ u3K0 5 x J) := by
    rw [hPK₀]; infer_instance
  have hxK : x ∈ u3K0 5 x J :=
    CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.x_mem_u3K0_gen hc
  have hxP : x ∈ (P : Subgroup G) := (Subgroup.zpowers_le.mpr hcP) hpres.x_mem
  obtain ⟨N₀, -, hN₀C, hN₀cop, hK⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.u3_K0_pComplement_core hc hPC hDcyc ⟨hxP, hxK⟩
      hpres.x_ord
  exact ⟨_, szh2_centSeries_of_comm hPW (fun c hc n hn => hN₀C c hc.2 n hn) hN₀cop hK
    (szh2_comm hS hD1 hU0 hSz hSz' hc hP)⟩

theorem sz32_case2_G (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hc : PointConfig IsSz32Type G 5 P M x J) {a c y : G} (hP : Sz32Struct P x J a c y)
    (hL : Sz32Lines P x (a ^ 5)) (hZ : Sz32ZFacts P M x (a ^ 5)) {N : Subgroup G}
    (hser : CentSeries 5 (M ⊓ Subgroup.centralizer ({x} : Set G)) (P : Subgroup G) N)
    (ha : a ∈ M) (hcM : c ∈ M) (hyM : y ∈ M) :
    Sz32Case2Data
      (((P : Subgroup G).subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) 5)))
      (QuotientGroup.mk' (primeComplementCore (G := ↥M) 5) ⟨a, ha⟩)
      (QuotientGroup.mk' (primeComplementCore (G := ↥M) 5) ⟨c, hcM⟩)
      (QuotientGroup.mk' (primeComplementCore (G := ↥M) 5) ⟨y, hyM⟩) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  have hMtop : M ≠ ⊤ := fun h => hc.not_le (h ▸ le_top)
  have hrank : CFSG.Open.pRank 5 M ≤ 3 := by
    have h1 := local_pRank_le_evenRank 5 (sigmaA_prime 5 hc.sigma) (sigmaA_odd 5 hc.sigma) M
      hc.core.1.1
    rw [hS.rank] at h1
    exact h1
  have hO := primeComplementCore_coprime (G := ↥M) 5
  have hNM : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ M :=
    normalizer_sylow_le hS hc.sigma hc.core
  have hpres := szh2_pres_Y hO hP hPM ha hcM hyM
  obtain ⟨g, hgN, hgswap⟩ := szh2_swap_Y (O := primeComplementCore (G := ↥M) 5) hP hL hNM ha hcM
  refine
    { core := primeComplementCore_quotient_eq_bot 5
      catalog := (CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.kProper M hMtop).quotient _
      rank := szh2_rank_quot (by norm_num) M hrank
      sylow := ?_
      pres := hpres
      facts := sz32_pgroup_struct hpres hgN hgswap
      swap := ⟨g, hgN, hgswap⟩
      wc := szh2_wc_Y hO hP hZ hPM ha hcM
      irr := szh2_irr_Y hP hZ hPM ha hcM
      perf := szh2_perf_Y hS hU0 hc
      series := szh2_series_Y hP hser hcM }
  obtain ⟨T', hT'⟩ := szh2_sylow_subgroupOf P hPM
  exact ⟨T'.mapSurjective (QuotientGroup.mk'_surjective _), by rw [Sylow.coe_mapSurjective, hT']⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
