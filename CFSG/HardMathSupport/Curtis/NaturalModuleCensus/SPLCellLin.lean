module

public import CFSG.HardMathSupport.Curtis.Coordinator.SPLCellFam
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellLinInner
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellLinTwo

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellLin

open CFSG.HardMathSupport.Curtis.Coordinator

theorem splLieInnerCellFam_A : SPLLieInnerCellFam IsIdxA := by
  intro S _ _ d hd hF ⟨e⟩ p r hp hp2 hr hr1 hr2
  obtain ⟨r0, q, hdq⟩ := hF
  obtain ⟨idx, hv⟩ := d
  obtain rfl : idx = .A r0 q := hdq
  have hq : q.p = 2 := hd
  obtain ⟨K, _, _, _, f, hf, hK, hn2, h4, ⟨eK⟩⟩ := exists_projectiveSL_of_typeA r0 q hv hq e
  obtain ⟨hr5, -⟩ := prime_facts hp hp2 hr hr1 hr2
  obtain ⟨hrp, hr3, hrne⟩ := SPLCell.prime_facts' hp hr hr1 hr2
  refine SPLCellFor.of_mulEquiv eK ?_
  by_cases hn : r0 + 1 = 2
  · obtain rfl : r0 = 1 := by omega
    exact splCellFor_projectiveSL_two (by rw [hK]; exact h4 hn) hp hp2 r
  · exact fun Ē ζ γ hE hcard hζp hζE hsolv hγ hγE hcomm hnt =>
      lin_cell_false (by omega) hf hK hp hp2 hr hr5 hrp hr2 hr3 hrne Ē hE hcard ζ γ hζp hζE hsolv
        hγ hγE hcomm hnt

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellLin
