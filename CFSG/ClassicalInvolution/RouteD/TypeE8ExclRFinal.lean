module

public import CFSG.ClassicalInvolution.RouteD.TypeE8ExclR1
public import CFSG.ClassicalInvolution.RouteD.TypeE8ExclR2Main
public import CFSG.ClassicalInvolution.RouteD.TypeE8ExclP1x
public import CFSG.ClassicalInvolution.ModelFacts.E8ExclStar
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

namespace CFSG.ClassicalInvolution.RouteD.TypeE8

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime]

theorem e8ClassExcluded (hLayer : E7LayerEquiv p f) (hConn : Fund12Connected p f)
    (hRow : E8D8Row' p f) (hD8 : E8D8NoThreeAdj p f) : E8ClassExcluded p f := by
  intro G _ _ _ hnab K z S hshape c β hβ t htβ hKβ ht g p₀ hT
  by_contra h6
  have hMFZ : Gaps.FundNoncentral p := Gaps.fundNoncentral p
  have hB8 : E7FrameRelations p f := ModelFacts.E7Model.e7FrameRelations S.odd S.five
  have hB9 : E7FrameInvolutions p f := ModelFacts.E7Model.e7FrameInvolutions S.odd S.five
  have hB7 : E7PerpA2StarFree p f := ModelFacts.E7Model.e7PerpA2StarFree S.odd S.five
  have hsingle : ∀ L ∈ 𝒞 K, ∃ g : G, L = conjSub g K := single_class K
  have hcases : p₀ = 0 ∨ p₀ = 1 ∨ p₀ = 2 ∨ p₀ = 3 ∨ p₀ = 4 ∨ p₀ = 5 := by
    fin_cases p₀ <;> simp_all
  have hR1 : (p₀ = 0 ∨ p₀ = 2 ∨ p₀ = 3 ∨ p₀ = 5) → False := fun h =>
    e8R1Excluded hMFZ hB8 hB7 G hnab K z S hshape c β hβ t htβ hKβ ht g p₀ h hT
  have hR2 : (p₀ = 1 ∨ p₀ = 4) → False := fun h =>
    r2_false' hMFZ hB8 hB9 hLayer hConn hRow hD8 (e8P1x (p := p) (f := f)) hnab S hshape c hβ htβ
      hKβ ht g h hT
  rcases hcases with h | h | h | h | h | h
  · exact hR1 (Or.inl h)
  · exact hR2 (Or.inl h)
  · exact hR1 (Or.inr (Or.inl h))
  · exact hR1 (Or.inr (Or.inr (Or.inl h)))
  · exact hR2 (Or.inr h)
  · exact hR1 (Or.inr (Or.inr (Or.inr h)))

end CFSG.ClassicalInvolution.RouteD.TypeE8
