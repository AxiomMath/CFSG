module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcOrthAll
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2F4Main
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E6Main
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E7Main
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E8Main
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2TwMain
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

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.ModelFacts.Levi

variable {p : ℕ} [Fact p.Prime]

theorem a2BranchLeft_exceptional {t : StatedLieTag} {e : ℕ}
    (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6)
    (hadm : StatedLieAdmissible t 0 p e) (hF4 : A2UnitaryF4 p e) (hE6 : A2UnitaryE6 p e)
    (hE7 : A2UnitaryE7 p e) (hE8 : A2UnitaryE8 p e) (hTw : A2UnitaryTw p e) :
    A2BranchLeft p t 0 e := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact a2BranchLeft_f4 hadm hF4
  · exact a2BranchLeft_e6 hadm hE6
  · exact a2BranchLeft_e7 hadm hE7
  · exact a2BranchLeft_e8 hadm hE8
  · exact a2BranchLeft_twistedE6 hadm hTw

theorem standardPairDichotomyFE_of_unitary (hF4 : ∀ e, A2UnitaryF4 p e)
    (hE6 : ∀ e, A2UnitaryE6 p e) (hE7 : ∀ e, A2UnitaryE7 p e) (hE8 : ∀ e, A2UnitaryE8 p e)
    (hTw : ∀ e, A2UnitaryTw p e) : StandardPairDichotomyFE p :=
  standardPairDichotomyFE_of_a2BranchLeft fun _ e ht hadm =>
    a2BranchLeft_exceptional ht hadm (hF4 e) (hE6 e) (hE7 e) (hE8 e) (hTw e)

end CFSG.ClassicalInvolution.ModelFacts
