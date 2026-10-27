module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TitsStruct
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Case2AbDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2GenDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2K0
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Decomp
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2WSeries

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3K0 U3LineWC CentSeries TypeBorelMax
  u3_pdata_common u3_P_decomp_core u3_centSeries_core)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem titsBorelMax (hX : TitsFacts) : TypeBorelMax IsTitsType 5 :=
  fun K _ _ hK S H hH => hX.maximal K hK S H hH

theorem tits_pdata (hX : TitsFacts) (hc : PointConfig IsTitsType G 5 P M x J)
    (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G)) :
    PGroupDataAb 5 (P : Subgroup G) (u3T P x J) ((P : Subgroup G) ⊓ u3K0 5 x J) x := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hcard, hE, -⟩ := plane_T_structure hX.sylow hc
  have hSdec := plane_S_decomp hX.sylow hX.noOuter hc
  have hdec := u3_P_decomp_core hc hP (k := 2) hcard
    (fun K _ _ hK hz S hS => plane_aut_pgroup_card_dvd (hX.sylow K hK) (hX.noOuter K hK) hz S hS)
  obtain ⟨hTP, hDP, hsup, hinf, hcomm, hDcyc, hxD, hord⟩ := u3_pdata_common hc hP hSdec hdec
  exact ⟨hTP, hDP, hsup, hinf, hcomm, hcard, hE.2, hE.1, hDcyc, hxD, hord⟩

theorem tits_centSeries (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G) (hX : TitsFacts)
    (hc : PointConfig IsTitsType G 5 P M x J)
    (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G)) :
    ∃ N : Subgroup G, CentSeries 5 (M ⊓ Subgroup.centralizer ({x} : Set G)) (P : Subgroup G) N := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hcard, hE, -⟩ := plane_T_structure hX.sylow hc
  have hpd := tits_pdata hX hc hP
  exact u3_centSeries_core hS hD1 hU0 hc hP (tits_two_le_pRank hc.prime.one_lt hE hcard) hE.2 (titsBorelMax hX)
    hpd.D_cyc hpd.x_mem hpd.x_ord hpd.sup_eq.ge

theorem tits_F (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G) (hX : TitsFacts)
    (hc : PointConfig IsTitsType G 5 P M x J) :
    J ⊓ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G) ≤ M ∧
      (∀ f ∈ J ⊓ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G), ∀ t ∈ u3T P x J,
        f * t * f⁻¹ ∈ u3T P x J) ∧
      ∀ a ∈ u3T P x J, a ≠ 1 → ∀ b ∈ u3T P x J, b ≠ 1 →
        ∃ f ∈ J ⊓ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G), f * a * f⁻¹ = b := by
  obtain ⟨hFM, hFtrans⟩ := tits_NJ_trans hS hD1 hU0 hX hc
  exact ⟨hFM, fun f hf t ht => (Subgroup.mem_normalizer_iff.mp hf.2 t).mp ht, hFtrans⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
