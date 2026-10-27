module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellUniInner

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open NaturalModuleCensus.SPLCellUni

theorem splLieInnerCellFam_TwistedA : SPLLieInnerCellFam IsIdxTwistedA := by
  intro S _ _ d hd hF ⟨e⟩ p r hp hp2 hr hr1 hr2
  obtain ⟨r0, q, hdq⟩ := hF
  obtain ⟨idx, hv⟩ := d
  obtain rfl : idx = .twistedA r0 q := hdq
  have hq : q.p = 2 := hd
  obtain ⟨f, K, _, hU, hn, hne, ⟨eT⟩⟩ := exists_primeFormP_of_twistedA r0 q hv hq e
  have : Finite K := hU.finite
  exact SPLCellFor.of_mulEquiv eT fun Ē ζ γ hE hcard hζp hζE hsolv hγ hγE hcomm hnt =>
    uni_inner_false hU hn hne hp hp2 hr hr1 hr2 Ē ζ γ hE hcard hζp hζE hsolv hγ hγE hcomm hnt

end CFSG.HardMathSupport.Curtis.Coordinator
