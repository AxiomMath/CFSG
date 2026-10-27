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

namespace CFSG.ClassicalInvolution.RouteD.TWT9

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.Asc77

local notation "𝒞" => CoreAssembly.conjClass

set_option linter.unusedSectionVars false

section Row

variable {p f : ℕ} [Fact p.Prime]


theorem twinYPartnerLOn_minus (hcls : TwinInvolution p f) :
    TwinYPartnerLOn p f fun t n => t = .POmegaMinus ∧ 4 ≤ n := by
  intro G _ _ _ hnab K z S tY nY hrow hP hshape
  obtain ⟨rfl, hm⟩ := hP
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simpa using S.five
    · exact h
  obtain ⟨c⟩ := TCtx.nonempty_minus hm S.odd S.five S.inClass S.exact
    (CoreAssembly.mem_conjClass_self K) S.cls S.p1 hshape
  have hadm : StatedLieAdmissible .POmegaMinus nY p f := ⟨Fact.out, hf, hm⟩
  obtain ⟨β, hβ, ⟨t, ht⟩, hKβ, hfix⟩ := c.exists_partner_minus hm S.odd hadm (single_class K)
    hshape
  obtain ⟨T, e, J, J', w, e', s, hcfg⟩ := TWE.B3.twinYConfigL_of_partner' hcls hnab S hrow hshape c
    (TWS6.signFacts_minus S.odd hm S.five) hβ ht hKβ hfix
  exact ⟨T, e, J, J', w, e', β, s, hcfg⟩

theorem twinTDExistsCase_of_YL {m : ℕ} (hm : 4 ≤ m) {P : StatedLieTag → ℕ → Prop}
    (hP : P .POmegaMinus m) (hY1 : TwinYP1On p f P) (hY2 : TwinYTypeOn p f P)
    (hY3 : TwinYPartnerLOn p f P)
    (hY4 : TwinYPatternAtL p f .POmegaMinus m
      (fun Ω K β t => PartnerPatternMinus p f m Ω K β t)) :
    TwinTDExistsCase p f m := by
  intro G _ _ _ hnab K z S k hk hshape
  subst hk
  exact TWE.B3.twinY_exists_on_L (t := .POmegaMinus) (n := k)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hm⟩))))) hP hY1 hY2 hY3 hY4 hnab S hshape

theorem twinTDExistsCase_four_of_Y124L (hcls : TwinInvolution p f)
    (hY1 : TwinYP1On p f fun t n => t = .POmegaMinus ∧ n = 4)
    (hY2 : TwinYTypeOn p f fun t n => t = .POmegaMinus ∧ n = 4)
    (hY4 : TwinYPatternAtL p f .POmegaMinus 4
      (fun Ω K β t => PartnerPatternMinus p f 4 Ω K β t)) :
    TwinTDExistsCase p f 4 :=
  twinTDExistsCase_of_YL (m := 4) (by norm_num) ⟨rfl, rfl⟩ hY1 hY2
    (twinYPartnerLOn_mono (fun t n h => ⟨h.1, by omega⟩) (twinYPartnerLOn_minus hcls)) hY4

theorem twinTDExistsCase_four_of_visible_noCentral_YL (hΩall : HypOmegaModAll p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) (hcls : TwinInvolution p f)
    (hVis : TwinYVisibleOn p f fun t n => t = .POmegaMinus ∧ n = 4)
    (hNC : TwinYNoCentralOn p f fun t n => t = .POmegaMinus ∧ n = 4)
    (hY4 : TwinYPatternAtL p f .POmegaMinus 4
      (fun Ω K β t => PartnerPatternMinus p f 4 Ω K β t)) :
    TwinTDExistsCase p f 4 := by
  intro G _ _ _ hnab K z S m hm hshape
  exact twinTDExistsCase_four_of_Y124L hcls
    (TWS6.twinYP1On_minus4_of_visible S.odd S.five hΩall hP4 hH hcls hVis)
    (TWS6.twinYTypeOn_minus4_of_noCentral S.odd S.five hΩall hP4 hH hcls hVis hNC) hY4 G hnab K z S
    m hm hshape

end Row

end CFSG.ClassicalInvolution.RouteD.TWT9
