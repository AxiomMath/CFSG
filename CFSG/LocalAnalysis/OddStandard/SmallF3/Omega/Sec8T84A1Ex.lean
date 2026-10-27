module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A1Elem
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A1Frat

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84_kex_of (F : Sec8T84Base) : Sec8T84KEx := by
  intro G _ _ t L S z g B hctx
  obtain ⟨K, hK⟩ := sec8t84a1_exists_pre F.h8A F.h8B F.hM hctx
  obtain ⟨hcomm, hsq⟩ :=
    sec8t84a1_elem F.h8B hK (sec8t84a1_H_trans F.h8A F.h8B F.hM hK)
  exact ⟨K, ⟨hK.ctx, hK.le_C, hK.syl, hK.A_le, hK.card, hK.cent_t, hK.tau, hcomm, hsq,
    sec8t84a1_pre_center hK⟩⟩

end CFSG.OddStandard.SmallF3.Omega
