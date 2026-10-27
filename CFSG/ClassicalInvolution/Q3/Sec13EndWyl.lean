module

public import CFSG.ClassicalInvolution.Q3.Sec13End
import CFSG.ClassicalInvolution.Q3.Sec13EndDict
import CFSG.ClassicalInvolution.Q3.Sec13EndDEWyl
import CFSG.ClassicalInvolution.Q3.Sec13EndAE8

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

theorem twinSet_conjSub_eq_image {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (g : G)
    (L : Subgroup G) : twinSet Ω (conjSub g L) = conjSub g '' twinSet Ω L := by
  refine Set.Subset.antisymm ?_ ?_
  · intro M hM
    refine ⟨conjSub g⁻¹ M, ?_, conjSub_conjSub_inv g M⟩
    have hM' := twinSet_conj hΩ hM g⁻¹
    rwa [conjSub_inv_conjSub] at hM'
  · rintro _ ⟨J, hJ, rfl⟩
    exact twinSet_conj hΩ hJ g

namespace EndHyp

variable {Ω : Set (Subgroup G)}

theorem ncard_twinSet_eq_four_of_muIsoWylD4 (h : EndHyp Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) (hWyl : MuIsoWylD4 Ω W) {K : Subgroup G} (hK : K ∈ Ω) :
    (twinSet Ω K).ncard = 4 := by
  obtain ⟨R, hRΩ, hRD⟩ := h.exists_mem_dSet hW
  have hR4 := (h.ncard_twinSet_of_mem_dSet h.kPerp_eq_twinSet hW hRD).2.2 hWyl
  obtain ⟨g, rfl⟩ := h.thmD.trans R hRΩ K hK
  rw [twinSet_conjSub_eq_image h.thmD.hyp.conjInvariant g R,
    Set.ncard_image_of_injective _ (conjSub_injective g), hR4]

end EndHyp

section FrameCert


theorem endBranchWyl : EndBranchWyl := by
  intro G _ _ Ω h W hW hWyl
  have h9 := h.perp9
  by_cases hDE : ∃ K ∈ Ω, zGroup Ω = eGroup Ω K
  · obtain ⟨K, hK, hDE⟩ := hDE
    exact (h.aeIdentOn_e29_of_zGroup_eq h9 hK hDE
      (h.ncard_twinSet_eq_four_of_muIsoWylD4 hW hWyl hK)).elim h.no_e29.false
  · push_neg at hDE
    exact h.false_of_wyl_ne h9 hW hWyl hDE

end FrameCert

end CFSG.ClassicalInvolution.Q3.Sec13
