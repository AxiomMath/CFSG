module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A2L1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A2Inv

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84_kl1_of (F : Sec8T84Base) (hK : Sec8T84KEx) : Sec8T84KL1 := by
  intro G _ _ t L S z g B hctx
  obtain ⟨K, hKK⟩ := hK G t L S z g B hctx
  obtain ⟨L1, hle, hBL, hcard, ht, hsup, hinvH⟩ := sec8t84a2_exists_L1 F.h8B hKK
  exact ⟨K, L1, ⟨hKK, hle, hBL, hcard, ht, hsup,
    sec8t84a2_inv F.h8A F.h8B F.hM hKK hle hBL hinvH⟩⟩

end CFSG.OddStandard.SmallF3.Omega
