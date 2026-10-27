module

public import CFSG.ClassicalInvolution.Q3.Sec13EndDEWylH

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

namespace DE4Hyp

variable {Ω : Set (Subgroup G)} (h : DE4Hyp Ω)
include h

theorem nonempty_aeIdentOn_e29_of_aglPts (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0)
    (P : AGLPts S b) : Nonempty (AEIdentOn Ω 8 AE.e29Sets AE.e29Sub) :=
  h.nonempty_aeIdentOn_e29_of_aglPts' S hb P

theorem nonempty_aeIdentOn_e29 : Nonempty (AEIdentOn Ω 8 AE.e29Sets AE.e29Sub) := by
  obtain ⟨S⟩ := h.exists_twinShift
  obtain ⟨P⟩ := h.exists_aglPts S (b := ((1 : ZMod 2), (0 : ZMod 2))) (by decide)
  exact h.nonempty_aeIdentOn_e29_of_aglPts S (b := ((1 : ZMod 2), (0 : ZMod 2))) (by decide) P

end DE4Hyp

namespace EndHyp

variable {Ω : Set (Subgroup G)} (h : EndHyp Ω)
include h

theorem aeIdentOn_e29_of_zGroup_eq (h9 : Perp9 Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hDE : zGroup Ω = eGroup Ω K) (hV : (twinSet Ω K).ncard = 4) :
    Nonempty (AEIdentOn Ω 8 AE.e29Sets AE.e29Sub) := by
  have hD : DEHyp Ω := h.dEHyp_of_zGroup_eq h9 hK hDE
  exact DE4Hyp.nonempty_aeIdentOn_e29
    (show DE4Hyp Ω from ⟨hD, fun L hL => (hD.twinSet_ncard_eq hL hK).trans hV⟩)

end EndHyp

end CFSG.ClassicalInvolution.Q3.Sec13
