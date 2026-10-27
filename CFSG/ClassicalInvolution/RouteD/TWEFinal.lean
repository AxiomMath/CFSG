module

public import CFSG.ClassicalInvolution.RouteD.TWELarge
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

namespace CFSG.ClassicalInvolution.RouteD.TWE

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.Asc77

set_option linter.unusedSectionVars false

section Final

variable {p f : ℕ} [Fact p.Prime]

theorem twinDExistsCase_six_of_residuals (hΩall : HypOmegaModAll p f)
    (hAT : AEmptyTwinRowOn p f TwinRow.large) (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f)
    (hcls : TwinInvolution p f)
    (hY4 : TwinYPatternAt p f .POmegaPlus 6 (@PartnerPatternD p f 6 _)) :
    TwinDExistsCase p f 6 := by
  intro G _ _ _ hnab K z S m hm hshape
  exact twinDExistsCase_of_Y (m := 6) (by norm_num) (P := TwinRow.large)
    (Or.inl ⟨rfl, by norm_num⟩)
    (twinYP1On_large_of_aEmptyTwinRow S.odd S.five hΩall hAT hP4 hH)
    (twinYTypeOn_large_of_aEmptyTwinRow S.odd S.five hΩall hAT hP4 hH)
    (TWD.twinYPartnerOn_large hcls) hY4 G hnab K z S m hm hshape

theorem twinDExistsSmall₄₆_of_four (h4 : TwinDExistsCase p f 4) (hΩall : HypOmegaModAll p f)
    (hAT : AEmptyTwinRowOn p f TwinRow.large) (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f)
    (hcls : TwinInvolution p f)
    (hY4 : TwinYPatternAt p f .POmegaPlus 6 (@PartnerPatternD p f 6 _)) :
    TwinDExistsSmall₄₆ p f := by
  intro G _ _ _ hnab K z S m hm hshape
  rcases hm with rfl | rfl
  · exact h4 G hnab K z S 4 rfl hshape
  · exact twinDExistsCase_six_of_residuals hΩall hAT hP4 hH hcls hY4 G hnab K z S 6 rfl hshape

end Final

end CFSG.ClassicalInvolution.RouteD.TWE
