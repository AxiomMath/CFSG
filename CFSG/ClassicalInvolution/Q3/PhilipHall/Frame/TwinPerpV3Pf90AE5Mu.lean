module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf56AE5
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf4Layer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf90AE5MuSec

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open scoped commutatorElement

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

section AE5MuProof


theorem v3SecAE5MuE4_proved (n : ℕ) : V3SecAE5MuE4 n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ hin hI
  obtain ⟨I⟩ := hI
  have hStd := hin.1
  exact AE5Mu.exists_W_muIsoE4 (layer_q8Section hStd.perp hStd.datum.sq_12) I

end AE5MuProof

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
