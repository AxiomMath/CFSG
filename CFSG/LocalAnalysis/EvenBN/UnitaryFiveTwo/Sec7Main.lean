module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec7Gen2
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec7NonSwap
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec7Bridge
public import CFSG.Yardstones.M41b0c98b3153.Definitions

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

theorem u52UnitaryCaseExclusion_of_unitaryProduct
    (hP : UnitaryProduct) :
    CFSG.Yardstones.M41b0c98b3153.U52UnitaryCaseExclusion := by
  intro G _ _ d h hKU
  obtain ⟨A, hU⟩ := hP G d h hKU
  have := h.simple
  exact Common.false_of_swap_configuration h.t_two h.isSimpleGroup_L h.not_comm_L h.even_card_L
    h.L_le_H (fun H hH hp => h.perfect_le hp hH) (h.isQuasisimple hU) (h.odd_center hU)
    (Subgroup.commutator_eq_bot_iff_le_centralizer.1 (by rw [commutator_comm]; exact hU.comm))
    (fun x hx => h.delta_mem_L hU hx) (h.delta_surj hU) h.isSylowOf_R hU.normalizer_R
    (fun H hN hp => h.perfect_le_sup hU H hp hN)
    (fun g htA htB => h.false_of_normalizes_both hU g htA htB)

theorem u52UnitaryCaseExclusion_of_commutation
    (hcomm : UnitaryCommutation) :
    CFSG.Yardstones.M41b0c98b3153.U52UnitaryCaseExclusion :=
  u52UnitaryCaseExclusion_of_unitaryProduct (unitaryProduct_of_commutation hcomm)

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
