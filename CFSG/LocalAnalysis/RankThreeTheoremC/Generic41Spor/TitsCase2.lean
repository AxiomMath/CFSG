module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupTits
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TitsCase2Data
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Case2AbCore
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2QuotData
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Quot
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PointConfigCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Lemma42Generic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 U3LineWC GenericComponentClass
  case2DataAb_of_G normalizes_of_quotient_normal)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem tits_normal_core (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hInn : KFactInnerAction) (hWC : KFactWeakClosure) (hX : TitsFacts)
    (hc : PointConfig IsTitsType G 5 P M x J)
    (hfus : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) ∧ U3LineWC x (P : Subgroup G)) :
    M ≤ Subgroup.normalizer ((u3T P x J ⊔ rankThreePrimeCore 5 M : Subgroup G) : Set G) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hPC, hwc⟩ := hfus
  have hpd := tits_pdata hX hc hPC
  obtain ⟨hFM, hFT, hFtrans⟩ := tits_F hS hD1 hU0 hX hc
  obtain ⟨N, hser⟩ := tits_centSeries hS hD1 hU0 hX hc hPC
  have hMtop : M ≠ ⊤ := fun h => hc.not_le (h ▸ le_top)
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  have hrank : CFSG.Open.pRank 5 M ≤ 3 := by
    have h1 := local_pRank_le_evenRank 5 (sigmaA_prime 5 hc.sigma) (sigmaA_odd 5 hc.sigma) M
      hc.core.1.1
    rw [hS.rank] at h1
    exact h1
  have hxM : x ∈ M := hPM (hpd.D_le hpd.x_mem)
  have hdata := case2DataAb_of_G hc.five hS.kProper hMtop hPM hrank hxM hpd hFM hFT hFtrans hser hwc
  have hnorm := case2_core_ab hdata hInn hWC
  exact normalizes_of_quotient_normal (hpd.T_le.trans hPM) hnorm

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
