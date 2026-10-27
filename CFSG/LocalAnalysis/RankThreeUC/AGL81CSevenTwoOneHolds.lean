module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CInputs
import CFSG.Quasithin.Vol2.Ch11SKFIto

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

theorem kFactOmegaNotCentral_holds : KFactOmegaNotCentral := by
  intro X _ _ _ C hC p hp hp2 hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsPerfect ↥C := hC.1.1
  obtain ⟨x, hxp, hxcent⟩ :=
    CFSG.Quasithin.Vol2.Ch11.SecS.KF.exists_pow_eq_one_not_mem_center (L := ↥C) hp2 hdvd
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hxcent (Subgroup.mem_center_iff.mpr fun g => by simp)
  have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
  obtain ⟨c, hc⟩ : ∃ c : ↥C, c * x ≠ x * c := by
    by_contra h
    push Not at h
    exact hxcent (Subgroup.mem_center_iff.mpr h)
  refine ⟨x, x.2, ?_, c, c.2, ?_⟩
  · simpa only [Subgroup.orderOf_coe] using hxord
  · intro h
    exact hc.symm (Subtype.ext h)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
