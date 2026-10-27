module

public import CFSG.ClassicalInvolution.RouteD.TWT4Fus
public import CFSG.ClassicalInvolution.RouteD.TWZSu4Odd
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

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.RouteD.NonClassical CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.RouteD.TWZ
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.RouteD.TWT4

section Assemble

variable {p f : ℕ} [Fact p.Prime]

theorem ne_two_of_mod_four_eq_three (hmod : (p ^ f) % 4 = 3) : p ≠ 2 := by
  rintro rfl
  rcases f with _ | _ | f
  · simp at hmod
  · simp at hmod
  · rw [pow_succ, pow_succ] at hmod
    omega

theorem twinYRankOn_psu4_of_p1' (hmod : (p ^ f) % 4 = 3)
    (hY1 : TwinYP1On p f fun t n => t = .PSU ∧ n = 4) :
    TwinYRankOn p f fun t n => t = .PSU ∧ n = 4 := by
  by_cases h5 : 5 ≤ p ^ f
  · exact twinYRankOn_psu4_of_p1 (ne_two_of_mod_four_eq_three hmod) h5 hmod hY1
  · intro G _ _ _ hnab K z S
    exact absurd S.five h5

theorem twinSU4Three_of_fusion (hΩall : HypOmegaModAll p f) (hAE : AEmptyTwinExact p f)
    (hcls : TwinInvolution p f) (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f)
    (hF : TwinSU4Fusion p f) : TwinSU4Three p f := by
  intro hmod
  have hp2 : p ≠ 2 := ne_two_of_mod_four_eq_three hmod
  have hV := twinYVisibleOn_of_fusion hF hmod
  have hNC := twinYNoCentralOn_of_fusion hF hmod
  have hPL : ∀ t n, (t = .PSU ∧ n = 4) → ListedTwin t n := fun t n h =>
    Or.inr (Or.inr (Or.inl h))
  have hGen : TwinYGenTOn p f fun t n => t = .PSU ∧ n = 4 := by
    by_cases h5 : 5 ≤ p ^ f
    · exact twinYGenTOn_of_model fun t n _ hP => by
        obtain ⟨rfl, rfl⟩ := hP
        exact twinMFGeneration_psu4 hp2 h5
    · intro G _ _ _ hnab K z S
      exact absurd S.five h5
  have hP1 := TWS.twinYP1On_of_visible_row hPL hΩall hAE hcls hP4 hH hGen hV
  exact ⟨hV, hNC, twinYRankOn_psu4_of_p1' hmod hP1, twinYLinkedSU4_of_mod_three p f hmod⟩

end Assemble

end CFSG.ClassicalInvolution.RouteD.TWT4
