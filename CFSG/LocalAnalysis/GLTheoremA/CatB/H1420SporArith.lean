module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamSpor

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.HardMathSupport.Solomon.Coordinator

theorem eq_M_of_three_mul_fi24_dvd (t : TauCeti.SporadicName)
    (h : 3 * sporOrd .Fi24Prime ∣ sporOrd t) : t = .M := by
  revert h
  cases t <;> decide +kernel

theorem eq_M_of_five_mul_hn_dvd (t : TauCeti.SporadicName)
    (h : 5 * sporOrd .HN ∣ sporOrd t) : t = .M := by
  revert h
  cases t <;> decide +kernel

end CFSG.LocalAnalysis.GLTheoremA.H1420
