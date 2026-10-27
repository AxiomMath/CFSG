module

public import CFSG.ClassicalInvolution.RouteD.TWEB3LPartner
public import CFSG.ClassicalInvolution.RouteD.TWS6SRow
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

namespace CFSG.ClassicalInvolution.RouteD.TWE.B3

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.Asc77

set_option linter.unusedSectionVars false

section Row

variable {p f : ℕ} [Fact p.Prime]


theorem twinBExistsCase_three_of_Y124L (hcls : TwinInvolution p f)
    (hY1 : TwinYP1On p f fun t n => t = .POmegaOdd ∧ n = 3)
    (hY2 : TwinYTypeOn p f fun t n => t = .POmegaOdd ∧ n = 3)
    (hY4 : TwinYPatternAtL p f .POmegaOdd 3 (@PartnerPatternBPair p f 3 _)) :
    TwinBExistsCase p f 3 :=
  twinBExistsCase_of_YL (m := 3) (by norm_num) ⟨rfl, rfl⟩ hY1 hY2
    (twinYPartnerLOn_mono (fun t n h => ⟨h.1, by omega⟩) (twinYPartnerLOn_odd hcls)) hY4

theorem twinBExistsCase_three_of_visible_noCentral_YL (hΩall : HypOmegaModAll p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) (hcls : TwinInvolution p f)
    (hVis : TwinYVisibleOn p f fun t n => t = .POmegaOdd ∧ n = 3)
    (hNC : TwinYNoCentralOn p f fun t n => t = .POmegaOdd ∧ n = 3)
    (hY4 : TwinYPatternAtL p f .POmegaOdd 3 (@PartnerPatternBPair p f 3 _)) :
    TwinBExistsCase p f 3 := by
  intro G _ _ _ hnab K z S m hm hshape
  exact twinBExistsCase_three_of_Y124L hcls
    (TWS6.twinYP1On_odd3_of_visible S.odd S.five hΩall hP4 hH hcls hVis)
    (TWS6.twinYTypeOn_odd3_of_noCentral S.odd S.five hΩall hP4 hH hcls hVis hNC) hY4 G hnab K z S m
    hm hshape

end Row

end CFSG.ClassicalInvolution.RouteD.TWE.B3
