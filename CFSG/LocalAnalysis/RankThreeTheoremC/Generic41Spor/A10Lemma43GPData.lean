module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Case2AbDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2K0
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Decomp
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PlaneStruct

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3K0 u3_pdata_common u3_P_decomp_core)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem a10_pdata (hX : A10Facts) (hc : PointConfig IsA10Type G 5 P M x J)
    (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G)) :
    PGroupDataAb 5 (P : Subgroup G) (u3T P x J) ((P : Subgroup G) ⊓ u3K0 5 x J) x := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hcard, hE, -⟩ := plane_T_structure hX.sylow hc
  have hSdec := plane_S_decomp hX.sylow hX.noOuter hc
  have hdec := u3_P_decomp_core hc hP (k := 2) hcard
    (fun K _ _ hK hz S hS => plane_aut_pgroup_card_dvd (hX.sylow K hK) (hX.noOuter K hK) hz S hS)
  obtain ⟨hTP, hDP, hsup, hinf, hcomm, hDcyc, hxD, hord⟩ := u3_pdata_common hc hP hSdec hdec
  exact ⟨hTP, hDP, hsup, hinf, hcomm, hcard, hE.2, hE.1, hDcyc, hxD, hord⟩

theorem a10_P_comm (hX : A10Facts) (hc : PointConfig IsA10Type G 5 P M x J)
    (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G)) :
    IsMulCommutative (P : Subgroup G) := by
  have hpd := a10_pdata hX hc hP
  haveI : IsMulCommutative ↥(u3T P x J) := hpd.T_comm
  haveI : IsMulCommutative ↥((P : Subgroup G) ⊓ u3K0 5 x J) := by
    haveI := hpd.D_cyc
    exact inferInstance
  have h := plane_sup_comm (A := u3T P x J) (B := (P : Subgroup G) ⊓ u3K0 5 x J) hpd.comm
  rwa [hpd.sup_eq] at h

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
