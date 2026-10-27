module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.EndSylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.EndHS
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.BridgeMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Cores

public section

namespace CFSG.OddStandard.SmallF3.L33

open CFSG.ComponentClassification CFSG.ComponentClassification.HSFLit

theorem smallF3L33Core_of_inputs
    (hGH74 : UFrontier.GH74ModelsInput) (hH : HaradaInput) (hGH : GorensteinHarrisInput) :
    SmallF3L33Core := by
  intro G _ _ L hS hC hL
  haveI := hS.simple
  obtain ⟨t, h⟩ := fritzHyp_of_smallF3 hGH74 hS hC hL
  exact false_of_ghRel_sylow hGH h (exists_ghRel_sylow hH hS.nonab h)

end CFSG.OddStandard.SmallF3.L33
