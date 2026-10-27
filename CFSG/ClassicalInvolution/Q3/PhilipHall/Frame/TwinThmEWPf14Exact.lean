module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf12Six
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12Coprime
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinOddCent

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.TC.Thin

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section Exact


variable [PrintedQuotOdd] [PrintedQuotCent] [PrintedHull]

theorem exactO2Q8_proved : ExactO2Q8 := by
  intro G _ _ Ω K S R W H c z hz Q hQn hQ2 hzQ J hJ
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  obtain ⟨g, rfl⟩ := e18_3Q8 G Ω K S R W H c J hJ
  have hzJ := hz.conj g
  have hzQ' : g * z * g⁻¹ ∈ Q := hQn.conj_mem z hzQ g
  have hodd := TwinExitPf12.oddCoreIn_centralizer_eq_bot_of_mem_normal c.oddCore_eq_bot hQn hQ2 hzQ'
  exact isPGroup_of_oddCent hΩ (hΩ.conjInvariant g K c.stand.mem) hzJ hodd
    (c.stand.two _ (hΩ.conjInvariant g K c.stand.mem))

end Exact

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
