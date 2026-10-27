module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf14BenderSz
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf10End
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf11Bender

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section Fin10

variable [PrintedQuotOdd] [PrintedQuotCent] [PrintedHull]

theorem e178BenderQ8_of' (h2 : E178U3Q8) : E178BenderQ8 := by
  have h1 := CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.BenderSz.benderNoQ8'
  intro G _ _ Ω K S R W H c z hz hSyl hFs hnab hFc hB hSE
  obtain ⟨P, -, ⟨eP⟩⟩ := c.stand.q8 K c.stand.mem
  rcases hB with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · exact h1 G (Subgroup.normalClosure ({z} : Set G)) hFc (Or.inl ⟨n, hn, ⟨e⟩⟩) P ⟨eP⟩
  · exact h1 G (Subgroup.normalClosure ({z} : Set G)) hFc (Or.inr ⟨n, hn, ⟨e⟩⟩) P ⟨eP⟩
  · exact h2 G Ω K S R W H c z hz hSyl hFs hnab hFc ⟨n, ⟨e⟩⟩ hSE

end Fin10

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
