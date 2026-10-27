module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F7E0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F5Cent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F2Str
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F4Nrm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F6Sw

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84f_TK_of (F : Sec8T84Base) (hI : Asc82Step84IK) (h811 : Asc82Lemma811K)
    (hSw : Sec8T84OuterSwaps) (hP : Sec8T84FactP) : Asc82Step84TK := by
  intro G _ _ hKP t L S z g B E hE hgood T hT hST hTS
  have hctx := hE.ctx
  have ht : t * t = 1 := by
    rw [← pow_two, ← hctx.involution]
    exact pow_orderOf_eq_one t
  have hinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have htS : t ∈ S := sec4_t_mem_S hctx.sylow hctx.involution
  have htN : t ∈ normalizer (E : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro e
    refine ⟨fun he => hE.t_norm e he, fun he => ?_⟩
    have h := hE.t_norm (t * e * t⁻¹) he
    have hkey : t * (t * e * t⁻¹) * t⁻¹ = e := by
      rw [hinv]
      calc t * (t * e * t) * t = (t * t) * e * (t * t) := by group
        _ = e := by rw [ht]; group
    rwa [hkey] at h
  have htT : t ∈ T := hST (Subgroup.mem_inf.mpr ⟨htS, htN⟩)
  obtain ⟨Y1, Y2, hXO⟩ := h811 G hKP t L S z g B E hE
  obtain ⟨F1, D⟩ := sec8t84_tdata_of hP ht hE.elem hXO hT htT
  have hrk := sec8t84_no_E8_cent_t F hI hKP hctx
  obtain ⟨u, hu⟩ := sec8t84_E0_conj F hI hSw hKP hE hgood hST D hrk
  have hET : E ≤ T := sec8t84_E_le_T D
  exact sec8t84_swap_contra hTS (sec8t84_E0_ne D).symm hET (sec8t84_E0_le_T D)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hET).mpr hT.1) (sec8t84_E0_normal D)
    hE.elem (sec8t84_E0_isElemAb2 D)
    (fun A hAT hA8 hAn => sec8t84_normal_E8 D hAT hA8 hAn) ⟨u, hu⟩

end CFSG.OddStandard.SmallF3.Omega
