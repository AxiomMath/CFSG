module

public import CFSG.ClassicalInvolution.SmallCases.NDBS1Cover
public import CFSG.ClassicalInvolution.SmallCases.NDBG5Use
public import CFSG.ClassicalInvolution.SmallCases.NDB5eMain
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
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance.Bootstrap

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime]

namespace S1

theorem exact_p1_of_frames {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G}
    {z : G} (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hz : IsClassicalMember p f K z) (hBelow : CITBelowU p f (Nat.card G))
    (hconn : Disconnected.DConnected (𝒞 K))
    (hfr : ∀ L ∈ 𝒞 K, ∀ w : G, IsClassicalMember p f L w → ¬ PSpShape p f (𝒞 K) w →
      ∃ (L₀ : Subgroup G) (z₀ : G) (A : Subgroup G) (S : Set (Subgroup G)) (a : G),
        Asc77.FuzzyFrameDataStarE p f (𝒞 K) L₀ z₀ A S a ∧ Asc77.Hyp51 A) :
    ExactMembers (𝒞 K) ∧ LocalOddCentral (𝒞 K) {z} := by
  have hP1 : LocalOddCentral (𝒞 K) {z} := by
    by_cases hE : PSpEverywhere p f (𝒞 K)
    · exact pspCaseP1Core_proved p f G K z ⟨hnab, hp2, hq, hz, hBelow, hconn⟩ hE
    · obtain ⟨L, hL, w, hw, hnot⟩ : ∃ L ∈ 𝒞 K, ∃ w : G, IsClassicalMember p f L w ∧
          ¬ PSpShape p f (𝒞 K) w := by
        by_contra hcon
        refine hE fun L hL w hw => ?_
        by_contra hn
        exact hcon ⟨L, hL, w, hw, hn⟩
      obtain ⟨L₀, z₀, A, S, a, hframe, hA⟩ := hfr L hL w hw hnot
      have hΩ := inClass_conjugates hz
      exact (Asc77.exactMembers_and_localOddCentral_of_fuzzyFrameStarE hnab hp2 hq hΩ
        (exists_single_class K) (localLieSystems_of_citBelowU hΩ hBelow) hconn hframe
        (Asc77.lemma52 G A hA)).2 K (mem_conjClass_self K) z hz
  exact ⟨SmallConn.exactMembers_of_localOddCentral exoticLeviBlock hnab hp2 hq hz hBelow hconn
    hP1, hP1⟩

end S1

end CFSG.ClassicalInvolution.NDB
