module

public import CFSG.ClassicalInvolution.RouteD.TypeE8ExclR2Basic
public import CFSG.ClassicalInvolution.RouteD.TypeE8ExclR2Corr
public import CFSG.ClassicalInvolution.RouteD.TypeE8Excl
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
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.RouteD.TypeE8Attached
public import CFSG.ClassicalInvolution.RouteD.TypeE8Witness
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor

public section

namespace CFSG.ClassicalInvolution.RouteD.TypeE8

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD.NonClassical (mem_centralizingMembers_pair Linked NCEdge)
open CFSG.ClassicalInvolution.RouteD.Gaps (commutes_symm)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

omit [Finite G] in
theorem le_centralizer_mul_of_le {w₁ w₂ : G} {L : Subgroup G}
    (h₁ : L ≤ Subgroup.centralizer ({w₁} : Set G)) (h₂ : L ≤ Subgroup.centralizer ({w₂} : Set G)) :
    L ≤ Subgroup.centralizer ({w₁ * w₂} : Set G) := fun k hk => by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have a := Subgroup.mem_centralizer_singleton_iff.mp (h₁ hk)
  have b := Subgroup.mem_centralizer_singleton_iff.mp (h₂ hk)
  calc k * (w₁ * w₂) = (k * w₁) * w₂ := by group
    _ = (w₁ * k) * w₂ := by rw [a]
    _ = w₁ * (k * w₂) := by group
    _ = w₁ * (w₂ * k) := by rw [b]
    _ = (w₁ * w₂) * k := by group

end CFSG.ClassicalInvolution.RouteD.TypeE8
