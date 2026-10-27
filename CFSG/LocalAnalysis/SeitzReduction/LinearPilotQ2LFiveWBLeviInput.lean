module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWA
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWBLevi

public section

namespace CFSG.SeitzReduction.LinearPilot

theorem pointRadicalLeviInput : PointRadicalLeviInput := fun _ _ _ hK c =>
  ⟨blockSL_compl_le_normalizer_pointRadical c,
    fun _ hv _ hw hv1 hw1 => exists_mem_blockSL_conj_eq_of_mem_pointRadical hK c hv hw hv1 hw1,
    exists_mem_blockSL_of_mulEquiv_pointRadical hK c,
    fun _ hl hlv => eq_one_of_mem_blockSL_of_forall_conj_pointRadical hK c hl hlv⟩

end CFSG.SeitzReduction.LinearPilot
