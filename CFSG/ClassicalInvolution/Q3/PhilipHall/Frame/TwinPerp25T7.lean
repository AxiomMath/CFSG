module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25T5
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25T6
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf62E4Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf15Final

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25T

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q8P.Asc77.P25R
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap


theorem p25_typedE4_proved
    : P25_TypedE4 := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 hbad hno hE
  have hC := twinSecCtx_of_bad hyp ha2 ha1 haA TwinThmE.t4Supply_proved
    (TwinDisc.oddCentEdge_proved _) hbad
  exact false_of_twinE4 hC (fun K hK z hz hO => hno ⟨K, hK, z, hz, hO⟩) hE
    TwinDisc.e4O8TwinModel_of_certs e4Sp6NC4Model_of_certs

end CFSG.ClassicalInvolution.Q8P.Asc77.P25T
