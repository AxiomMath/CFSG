module

public import CFSG.ClassicalInvolution.Q3.TA3FrameCases

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Frame

open CFSG CFSG.Open CFSG.Blueprint CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3.Q3T.MFS

variable {Y : Type} [Group Y] [Finite Y] {z : Y} {L T : Subgroup Y}

theorem false_of_excludedSmall (hl34 : SpecialFrame fun X _ => LieModel X .PSL 3 2 2)
    (hS : Setting z L T) (h3 : memberIndex L T = 3) (hF : TwoSubgroupsFourGenerated ↥T)
    (hex : Nobq.ExcludedSmall ↥T) : False := by
  have := hS.normal
  have hL := hS.member
  have hTL := hS.sup
  have hC := hS.cent
  rcases hex with h | h | h | h | h | h | ⟨n, hn8, -, h⟩ | h | h | h | h | h | h | h
  · obtain ⟨e⟩ := h
    exact false_of_not_three_dvd hTL h3 hC (not_three_dvd_alternating le_rfl e)
  · exact false_of_not_three_dvd hTL h3 hC (not_three_dvd_psu_three_four h)
  · exact false_of_noQ8 hL hTL h3 (noQ8_psl2_even (by norm_num) h)
  · exact false_of_noQ8 hL hTL h3 (noQ8_psl2_even (by norm_num) h)
  · exact hl34 Y z L T hS h3 hF h
  · exact false_of_noQ8 hL hTL h3 (noQ8_sz8 h)
  · obtain ⟨e⟩ := h
    exact false_of_not_three_dvd hTL h3 hC (not_three_dvd_alternating (by omega) e)
  · exact false_of_not_three_dvd hTL h3 hC (not_three_dvd_M22 h)
  · exact false_of_not_three_dvd hTL h3 hC (not_three_dvd_M23 h)
  · exact false_of_not_three_dvd hTL h3 hC (not_three_dvd_J1 h)
  · exact false_of_not_three_dvd hTL h3 hC (not_three_dvd_J2 h)
  · exact false_of_not_three_dvd hTL h3 hC (not_three_dvd_J3 h)
  · exact false_of_not_three_dvd hTL h3 hC (not_three_dvd_McL h)
  · exact false_of_not_three_dvd hTL h3 hC (not_three_dvd_Ly h)

end CFSG.ClassicalInvolution.Q3.TA3.Frame
