module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FiStep
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiNoStd

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open CFSG.Blueprint.NativeSporadic

section Certificates


theorem fiSmallFStar : FiSmallFStar := by
  intro H _ _ N hN hidx hNs L s hs hstd hcov
  have hs' : s = .Fi22 ∨ s = .Fi23 ∨ s = .Fi24Prime := by simpa [fiTypes] using hs
  rcases hNs with hNs | hNs
  · exact not_oddCover_fi22 hN hNs hidx hstd hs hcov
  · rcases hs' with rfl | rfl | rfl
    · exact not_oddCover_fi22_of_fi23 hN hNs hidx hstd hcov
    · exact not_oddCover_fi23_of_ge hN hNs hidx hstd (Or.inl rfl) hcov
    · exact not_oddCover_fi23_of_ge hN hNs hidx hstd (Or.inr rfl) hcov

end Certificates

end CFSG.EvenSporadicStandard.Induction
