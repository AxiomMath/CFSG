module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamSpor

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.HardMathSupport.Solomon.Coordinator

theorem eq_survivor_of_three_mul_u43_dvd (t : TauCeti.SporadicName)
    (h : 3 * 3265920 ∣ sporOrd t) :
    t = .Suz ∨ t = .Co3 ∨ t = .Co1 ∨ t = .Ly ∨ t = .Th ∨ t = .Fi22 ∨ t = .Fi23 ∨
      t = .Fi24Prime ∨ t = .B ∨ t = .M := by
  revert h
  cases t <;> decide +kernel

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
