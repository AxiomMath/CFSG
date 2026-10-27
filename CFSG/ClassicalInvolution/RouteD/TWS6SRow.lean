module

public import CFSG.ClassicalInvolution.RouteD.TWS6SRank
public import CFSG.ClassicalInvolution.RouteD.TWS6Cfg
public import CFSG.ClassicalInvolution.RouteD.TWEAssemble
public import CFSG.ClassicalInvolution.RouteD.TWEClose
public import CFSG.ClassicalInvolution.RouteD.SCRTwinGenSmall
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952

public section

namespace CFSG.ClassicalInvolution.RouteD.TWS6

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.Asc77

set_option linter.unusedSectionVars false

section Row

variable {p f : ℕ} [Fact p.Prime]

theorem twinYP1On_odd3_of_visible (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩall : HypOmegaModAll p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) (hcls : TwinInvolution p f)
    (hVis : TwinYVisibleOn p f fun t n => t = .POmegaOdd ∧ n = 3) :
    TwinYP1On p f fun t n => t = .POmegaOdd ∧ n = 3 :=
  TWE.twinYP1On_of_visible_rowT hΩall
    (TWE.AEmptyTwinRow.on (TWE.Big.aEmptyTwinRow_proved hΩall hcls)) hP4 hH
    (twinYGenTOn_of_model fun tY nY _ hl => by
      obtain ⟨rfl, rfl⟩ := hl
      exact twinMFGeneration_odd hp2 hq (le_refl 3))
    hVis

theorem twinYTypeOn_odd3_of_noCentral (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩall : HypOmegaModAll p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) (hcls : TwinInvolution p f)
    (hVis : TwinYVisibleOn p f fun t n => t = .POmegaOdd ∧ n = 3)
    (hNC : TwinYNoCentralOn p f fun t n => t = .POmegaOdd ∧ n = 3) :
    TwinYTypeOn p f fun t n => t = .POmegaOdd ∧ n = 3 :=
  TWE.twinYTypeOn_of_inputs_rowT hΩall
    (TWE.AEmptyTwinRow.on (TWE.Big.aEmptyTwinRow_proved hΩall hcls)) hP4
    (TWE.twinYTransitiveOn_of_p1_rowT hΩall
      (TWE.AEmptyTwinRow.on (TWE.Big.aEmptyTwinRow_proved hΩall hcls))
      (twinYP1On_odd3_of_visible hp2 hq hΩall hP4 hH hcls hVis) hNC)
    (twinYRankOn_odd3 hp2 hq (twinYP1On_odd3_of_visible hp2 hq hΩall hP4 hH hcls hVis))

theorem twinYP1On_minus4_of_visible (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩall : HypOmegaModAll p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) (hcls : TwinInvolution p f)
    (hVis : TwinYVisibleOn p f fun t n => t = .POmegaMinus ∧ n = 4) :
    TwinYP1On p f fun t n => t = .POmegaMinus ∧ n = 4 :=
  TWE.twinYP1On_of_visible_rowT hΩall
    (TWE.AEmptyTwinRow.on (TWE.Big.aEmptyTwinRow_proved hΩall hcls)) hP4 hH
    (twinYGenTOn_of_model fun tY nY _ hl => by
      obtain ⟨rfl, rfl⟩ := hl
      exact twinMFGeneration_minus hp2 hq (le_refl 4))
    hVis

theorem twinYTypeOn_minus4_of_noCentral (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩall : HypOmegaModAll p f) (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f)
    (hcls : TwinInvolution p f)
    (hVis : TwinYVisibleOn p f fun t n => t = .POmegaMinus ∧ n = 4)
    (hNC : TwinYNoCentralOn p f fun t n => t = .POmegaMinus ∧ n = 4) :
    TwinYTypeOn p f fun t n => t = .POmegaMinus ∧ n = 4 :=
  TWE.twinYTypeOn_of_inputs_rowT hΩall
    (TWE.AEmptyTwinRow.on (TWE.Big.aEmptyTwinRow_proved hΩall hcls)) hP4
    (TWE.twinYTransitiveOn_of_p1_rowT hΩall
      (TWE.AEmptyTwinRow.on (TWE.Big.aEmptyTwinRow_proved hΩall hcls))
      (twinYP1On_minus4_of_visible hp2 hq hΩall hP4 hH hcls hVis) hNC)
    (twinYRankOn_minus4 hp2 hq (twinYP1On_minus4_of_visible hp2 hq hΩall hP4 hH hcls hVis))

end Row

end CFSG.ClassicalInvolution.RouteD.TWS6
