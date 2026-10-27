module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameTwinCover
public import CFSG.ClassicalInvolution.Asc77.WP3FramePSCMain
public import CFSG.ClassicalInvolution.Asc77.AscIHSectE
public import CFSG.ClassicalInvolution.RouteD.TwinYP1Main
public import CFSG.ClassicalInvolution.RouteD.TriageP1Rows
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
public import CFSG.ClassicalInvolution.Asc77.WP3FrameP1

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD.TwinY

local notation "𝒞" => CoreAssembly.conjClass

section Inputs

variable (p f : ℕ) [Fact p.Prime]

@[expose] def TwinInvolution : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (tY : StatedLieTag) (nY : ℕ),
      TwinRow tY nY → LocalShapeT p f 2 tY nY (𝒞 K) z → ∀ T : Subgroup G,
      IsTwinAt (𝒞 K) K T z → IsClassicalMember p f T z

variable {p f}

theorem NoThreeFund.of_small {tY : StatedLieTag} {nY : ℕ} (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible tY nY p f)
    (hsmall : (tY = .PSp ∧ nY = 2) ∨ (tY = .PSL ∧ nY = 4) ∨ (tY = .PSU ∧ nY = 4) ∨
      (tY = .POmegaOdd ∧ nY = 3) ∨ (tY = .POmegaMinus ∧ nY = 4)) :
    NoThreeFund p f tY nY :=
  fun A hA B hB C hC => smallNoThree tY nY f hadm hp hq hsmall A hA B hB C hC

end Inputs

end CFSG.ClassicalInvolution.Asc77
