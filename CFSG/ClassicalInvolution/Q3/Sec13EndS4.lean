module

public import CFSG.ClassicalInvolution.Q3.Sec13End
import CFSG.ClassicalInvolution.Q3.Sec13EndDEQ2Iso
import CFSG.ClassicalInvolution.Q3.Sec13End16D

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

section FrameCert


theorem endBranchS4 : EndBranchS4 := by
  intro G _ _ Ω h W hW hS4
  have h9 := h.perp9
  obtain ⟨K, hK, -⟩ := h.exists_ne
  obtain ⟨K', hne, hV⟩ :=
    h.exists_twinSet_pair_of_exists_muIsoS4 h.kPerp_eq_twinSet ⟨W, hW, hS4⟩ K hK
  by_cases hDE : zGroup Ω = eGroup Ω K
  · have hV2 : (twinSet Ω K).ncard = 2 := by rw [hV, Set.ncard_pair hne.symm]
    exact (h.aeIdentOn_e64_of_zGroup_eq h9 hK hDE hV2).elim h.no_e64.false
  · exact h.false_of_twinSet_two h9 hK hV hne.symm hDE

end FrameCert

end CFSG.ClassicalInvolution.Q3.Sec13
