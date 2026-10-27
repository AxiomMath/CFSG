module

public import CFSG.ClassicalInvolution.SmallCases.NDBE9Final
import CFSG.ClassicalInvolution.SmallCases.NDBG3Proved
import CFSG.ClassicalInvolution.Asc77.AscBSE8
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
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
public import Certificates.Certificate82
public import Certificates.Certificate83
public import Certificates.Certificate84
public import Certificates.Certificate85
public import Certificates.Certificate86
public import Certificates.Certificate87
public import Certificates.Certificate88
public import Certificates.Certificate89
public import Certificates.Certificate90
public import Certificates.Certificate91
public import Certificates.Certificate92
public import Certificates.Certificate93
public import Certificates.Certificate94
public import Certificates.Certificate95
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate110
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
public import Certificates.Certificate3120
public import Certificates.Certificate3951
public import Certificates.Certificate3952
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8046
public import Certificates.Certificate8048
public import Certificates.Certificate8049
public import Certificates.Certificate8052

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance.Bootstrap

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime]


theorem bootNoG2D4Twin_proved : BootNoG2D4Twin p f := by
  intro G _ _ _ K z hS hT D i hi
  let C := Cover.toXCtx hS.nonabelian hS.odd hS.five hS.member hS.below D
  obtain ⟨T, hTΩ, hTK, hTz⟩ : ∃ T ∈ 𝒞 K, T ≠ K ∧ IsClassicalMember p f T z := hT
  have hb : ¬ (C.D.tag i = .PSL ∧ C.D.rank i = 2) := fun h => by
    rcases hi with h' | h'
    · rw [show C.D.tag i = .G2 from h'] at h
      exact absurd h.1 (by decide)
    · rw [show C.D.tag i = .trialityD4 from h'] at h
      exact absurd h.1 (by decide)
  have h3 : 3 ≤ C.D.card := NDBG.three_le_card_of_twin C hb hTΩ hTK hTz
  rcases hi with hG2 | hD4
  · exact bootNoG2Twin_proved G K z hS D i hG2 h3
  · exact NDBG.false_of_trialityD4_of_card (C := C) (Asc77.BSC.noFuzzyFrame hS) hD4 h3

theorem noDataBootD_of_narrowA (hA : NoAllA1Narrow p f) : SmallConn.NoDataBootD p f :=
  noDataBootD_of_residualsX (noAllA1_of_narrow hA) noG2D4Twin_proved
    (exoticNoTwinFrames_of_spin (exoticFrameSpin_proved p f))

theorem bootNoTripleD_of_narrowA (hA : NoAllA1Narrow p f) : Disconnected.BootNoTripleD p f :=
  bootNoTripleD_of_coverXW (bootShapeCoverX_of_residuals
      ⟨bootNoAllA1_of_narrow hA, bootNoG2D4Twin_proved, Asc77.BSC.BSD.bootNoM3Twin,
        Asc77.BSC.BSD.bootNoManyTwins
          (Asc77.BSC.BSE.bootNoManyTwinsD4_of_five bootNoD4FiveComp_proved)⟩)
    (exoticNoTwinFrames_of_spin (exoticFrameSpin_proved p f))

end CFSG.ClassicalInvolution.NDB
