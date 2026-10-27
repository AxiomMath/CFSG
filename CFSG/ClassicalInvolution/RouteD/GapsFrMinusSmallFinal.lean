module

public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusFinal
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusSmallPattern
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

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.WeakCT

variable {p f : ℕ} [Fact p.Prime]

@[expose] def TwinTDSmallPattern7 (p f : ℕ) [Fact p.Prime] : Prop :=
  TwinTDPatternOn p f fun m => 4 ≤ m ∧ m ≤ 7

theorem twinTDPatternOn_of_seven (hMFZ : FundNoncentral p) (hS : TwinTDSmallPattern7 p f) :
    TwinTDPatternOn p f fun m => 4 ≤ m := by
  intro G _ _ _ hnab K z S m hm hshape β hβ t ht hKβ hfix
  by_cases h8 : 8 ≤ m
  · obtain ⟨u, rfl⟩ : ∃ u, m = u + 3 + 5 := ⟨m - 8, by omega⟩
    obtain ⟨c⟩ := TCtx.nonempty_minus (by omega) S.odd S.five S.inClass S.exact
      (mem_conjClass_self K) S.cls S.p1 hshape
    exact PartnerPatternMinus.of_fixed_member_ge3 hMFZ c (single_class K) hshape hβ ht hKβ hfix
  · exact hS G hnab K z S m ⟨hm, by omega⟩ hshape β hβ t ht hKβ hfix

theorem twinTDSmallPattern_of_seven (hMFZ : FundNoncentral p) (hS : TwinTDSmallPattern7 p f) :
    TwinTDSmallPattern p f := by
  intro G _ _ _ hnab K z S m hm hshape β hβ t ht hKβ hfix
  exact twinTDPatternOn_of_seven hMFZ hS G hnab K z S m hm.1 hshape β hβ t ht hKβ hfix

end CFSG.ClassicalInvolution.RouteD.Gaps
