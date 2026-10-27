module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Core
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Decomp
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2TorusB
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2QuotData
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2WSeries
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Quot
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2TorusA
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Struct

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor (PointConfig pointConfig_of_u3)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
  {J : Subgroup G}

theorem u3_normal_core_proof_gen (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hInn : KFactInnerAction) (hWC : KFactWeakClosure) (h123 : KFactWeakClosureHeis)
    {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hc : PointConfig Typ G p P M x J)
    (hfus : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) ∧ U3LineWC x (P : Subgroup G)) (hTstr : TypeTStruct p P x J) (hSdec : TypeSDecomp p P x J) (hAut : TypeAutPCard Typ p)
    (hIrr : TypeTorusIrred Typ p) (hFpf : TypeTorusFpf Typ p) (hOn : TypeTorusOnCenter Typ p)
    (hmax : TypeBorelMax Typ p) :
    M ≤ Subgroup.normalizer ((u3T P x J ⊔ rankThreePrimeCore p M : Subgroup G) : Set G) := by
  haveI : Fact p.Prime := ⟨hc.prime⟩
  obtain ⟨hPC, hwc⟩ := hfus
  have hpd := u3_pdata_gen hc hPC hTstr hSdec hAut
  obtain ⟨F, hFM, hF, hFD⟩ := u3_exists_Fhat_gen hS hc hPC hpd hpd.sup_eq.ge
    (u3_torusProps_NJ_gen hc hIrr hFpf hOn)
  obtain ⟨N, hser⟩ := u3_centSeries_gen hS hD1 hU0 hc hPC hTstr hmax hpd
  have hMtop : M ≠ ⊤ := fun h => hc.not_le (h ▸ le_top)
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  have hrank : CFSG.Open.pRank p M ≤ 3 := by
    have h1 := local_pRank_le_evenRank p (sigmaA_prime p hc.sigma) (sigmaA_odd p hc.sigma) M
      hc.core.1.1
    rw [hS.rank] at h1
    exact h1
  have hxM : x ∈ M := hPM (hpd.D_le hpd.x_mem)
  have hdata := case2Data_of_G hc.five hS.kProper hMtop hPM hrank hxM hpd hF hFM hFD hser hwc
  have hnorm := case2_core hdata hInn hWC h123
  exact normalizes_of_quotient_normal (hpd.T_le.trans hPM) hnorm

theorem u3_normal_core_proof (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hInn : KFactInnerAction) (hWC : KFactWeakClosure) (h123 : KFactWeakClosureHeis)
    (hc : U3Config G p P M x J)
    (hfus : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) ∧ U3LineWC x (P : Subgroup G)) :
    M ≤ Subgroup.normalizer ((u3T P x J ⊔ rankThreePrimeCore p M : Subgroup G) : Set G) := by
  haveI : Fact p.Prime := ⟨hc.prime⟩
  exact u3_normal_core_proof_gen hS hD1 hU0 hInn hWC h123 (pointConfig_of_u3 hc) hfus (u3_T_structure hc)
    (u3_S_decomp hc) (typeAutPCard_u3 hc.five) (typeTorusIrred_u3 hc.five) (typeTorusFpf_u3 hc.five)
    (typeTorusOnCenter_u3 hc.five) typeBorelMax_u3

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
