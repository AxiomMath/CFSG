module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22N
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22DOpen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

section

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

variable {n : ℕ}

theorem v3ExitTrichotomyAd_of_open (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (h4 : Thm4RTwinBelow 3 n) (hEx : V3SecOpenW n) : V3ExitTrichotomyAd n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ hin W hW hKD hK'D hK₃D hu₁ hu₂
  have hMu := hEx Y R S t K K' K₃ u₁ u₂ u₃ K₄ hin W hW hKD hK'D hK₃D hu₁ hu₂
  have h3 := v3SecOrder_three_dvd_adapted hin hW hKD hK'D hK₃D hu₁ hu₂
  obtain ⟨hStd, hF, hα, h2g, hno⟩ := hin
  exact v3ExitResidual_open hcit hP h4 (oddCentEdge_proved n) hStd hF h2g hno h3 hMu

end

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
