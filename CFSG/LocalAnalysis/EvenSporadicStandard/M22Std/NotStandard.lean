module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.NotStandardInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.A6Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.CentralGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.XbarKGroup
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.M22Setup

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.M23Std

theorem not_dvd_card_of_isSporadic_M22 {Y : Type} [Group Y]
    (hY : IsSporadic Y .M22) : ¬ 256 ∣ Nat.card Y := by
  obtain ⟨e⟩ := hY
  have hM : Nat.card (Carrier .M22) = 443520 := CFSG.Sporadic.Mathieu.card_M22
  rw [Nat.card_congr e.toEquiv, hM]
  norm_num

theorem m22_inner_false_of_inputs
    (hSol : CFSG.EvenSporadicStandard.Fin76b.SolomonZ2A6) (hE : Fin76aWreathNoFusionM22)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : StdHyp G L) (hL : IsSporadic L .M22)
    {z : G} (hz : z ∈ centralizer (L : Set G)) (hz2 : orderOf z = 2)
    (hC : centralizer ({z} : Set G) ≤ L ⊔ zpowers z) : False := by
  have := h.simple
  obtain ⟨t, F, L1, N, htL, S, hnc, -, hA6, hFix⟩ := m22_setup h hL hz hz2 hC
  rcases Setup.xbar_dichotomy_gen S even_natCard_alternatingGroup_six
      center_alternatingGroup_six (solomonGen_six hSol) (S.isKGroupCat_xbar h) hA6 with hcen |
      ⟨N1, N2, hN1, hN2, hcomm, hdisj, hnorm, hidx, hz0, hconj⟩
  · exact Setup.false_of_central_gen S h.nonabelian even_natCard_alternatingGroup_six hFix hA6
      orderOf_sigma6 (not_dvd_card_of_isSporadic_M22 hL) hnc hcen
  · obtain ⟨P, hP, hzP, hT⟩ := S.exists_sylow_X (not_dvd_card_of_isSporadic_M22 hL)
    obtain ⟨g, hg⟩ := S.exists_conj_mem_preimage_of_wreath h.nonabelian hcomm hdisj hnorm hidx hz0
      hconj hP hzP hT
    exact hE G L h hL z t F L1 N hz hz2 hC S hnc hA6 N1 N2 hN1 hN2 hcomm hdisj hnorm hidx hz0 hconj
      g (mem_inf.1 hg).2

end CFSG.EvenSporadicStandard.M22Std
