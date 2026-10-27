module

public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorU
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorSp

public noncomputable section

namespace CFSG.ComponentClassification.OddClassSelector

open CFSG.ComponentClassification.RestrictedStd

theorem almostSimpleRestricted_oddClassical :
    AlmostSimpleRestricted OddClassicalUnrestricted := by
  intro A _ _ W _ hWs hWnab hCW _ hP a ha L hLW _ hL hstd hs
  obtain ⟨p, f, hp, hp2, hf, hfam⟩ := hP
  exfalso
  rcases hfam with ⟨n, hn, hM⟩ | ⟨n, hn, hM⟩ | hOrth
  · exact su_family_false hWs hWnab hCW ha hLW hL hs hp hp2 hf hn hM
  · exact sp_family_false hWs hWnab hCW ha hLW hL hstd hs hp hp2 hf hn hM
  · exact orth_family_false hWs hWnab hCW ha hLW hL hstd hs hp hp2 hf hOrth

end CFSG.ComponentClassification.OddClassSelector
