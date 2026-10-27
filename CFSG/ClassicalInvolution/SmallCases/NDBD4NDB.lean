module

public import CFSG.ClassicalInvolution.SmallCases.NDBD4Defs
public import CFSG.ClassicalInvolution.SmallCases.NDBD4Card
public import CFSG.ClassicalInvolution.SmallCases.NDBF
public import CFSG.ClassicalInvolution.Asc77.AscBSE7
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

namespace CFSG.ClassicalInvolution.NDB

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance

variable {p f : ℕ} [Fact p.Prime]

theorem noD4Twins_of (h : D4FiveCore p f) : NoD4Twins p f := by
  intro G _ _ _ K z hS hTT D i hi
  have hno := fuzzyFrameExcluded G K z hS
  let C := Cover.toXCtx hS.nonabelian hS.odd hS.five hS.member hS.below D
  obtain ⟨T₁, h₁, T₂, h₂, h1K, h2K, h12, h1z, h2z⟩ := hTT
  have hD4 : C.D.tag i = .POmegaPlus := hi.1
  have hrank : C.D.rank i = 4 := hi.2
  have hQ : ¬ (C.D.tag i = .PSL ∧ C.D.rank i = 2) := fun h' => by
    rw [hD4] at h'
    exact absurd h'.1 (by decide)
  have h4 : 4 ≤ C.D.card := D4.four_le_card C h₁ h₂ h1K h2K h12 h1z h2z hQ
  rcases (by omega : C.D.card = 4 ∨ C.D.card = 5 ∨ 6 ≤ C.D.card) with h4' | h5 | h6
  · exact Asc77.BSC.BSE.false_of_d4_four (C := C) hno (b := i) hD4 hrank h4'
  · exact h G K z hS.nonabelian hS.odd hS.five hS.member hS.below hS.dconn hno D i hi h5
  · exact Asc77.BSC.BSE.false_of_d4_many (C := C) hno (b := i) hD4 hrank h6

end CFSG.ClassicalInvolution.NDB
