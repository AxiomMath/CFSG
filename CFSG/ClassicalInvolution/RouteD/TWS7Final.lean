module

public import CFSG.ClassicalInvolution.RouteD.TWS7Model
public import CFSG.ClassicalInvolution.RouteD.TWS7Asm
public import CFSG.ClassicalInvolution.RouteD.TwinSmallCasesD
public import CFSG.ClassicalInvolution.RouteD.TwinYExistsD
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralBridge
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

namespace CFSG.ClassicalInvolution.RouteD.TWS7

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.RouteD.Gaps

set_option linter.unusedSectionVars false

section Final

variable {p f : ℕ} [Fact p.Prime]

theorem twinDExistsCase_four : TwinDExistsCase p f 4 := by
  intro G _ _ _ hnab K z S m hm hshape
  obtain rfl : m = 4 := hm
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simpa using S.five
    · exact h
  have hadm : StatedLieAdmissible .POmegaPlus 4 p f := ⟨Fact.out, hf, le_refl 4⟩
  obtain ⟨c⟩ := TCtx.nonempty_plus (le_refl 4) S.odd S.five S.inClass S.exact
    (mem_conjClass_self K) S.cls S.p1 hshape
  obtain ⟨β, hβ, ⟨t, ht⟩, hKβ, hfix⟩ := c.exists_partner_plus (le_refl 4) hadm (single_class K)
    hshape
  exact ⟨β, hβ, t, ht, hKβ, partnerPatternD_four_of_model modelLeafD_proved (fundNoncentral p) c
    (single_class K) hshape hβ ht hKβ hfix⟩

end Final

end CFSG.ClassicalInvolution.RouteD.TWS7
