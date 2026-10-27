module

public import Mathlib
public import CFSG.ClassicalInvolution.SmallCases.SmallConnSetup
public import CFSG.ClassicalInvolution.Generic.CoreAssembly
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

namespace CFSG.ClassicalInvolution.SmallConn

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Balance.Bootstrap

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem lieSystem_of_noDataBootD (hN : NoDataBootD p f)
    (hshape : ∀ (a : ℕ) (t : StatedLieTag) (n : ℕ), ShapePiece p f a t n)
    (hmulti : MultiPiece p f) (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z)
    (hBelow : CITBelowU p f (Nat.card G)) (h3 : 3 ≤ CFSG.Open.twoRank G)
    (h4 : ¬ TwoSubgroupsFourGenerated G) (hD : DConnected (𝒞 K))
    (hB : ¬ BootData p f (𝒞 K)) : LieSystem p f G (𝒞 K) := by
  obtain ⟨hex, hp1⟩ := hN G hnab hp2 hq K z hz hBelow h3 h4 hD hB
  have hconn : RouteD.DeltaConnected (𝒞 K) :=
    routeD_deltaConnected_of_dConnected_of_exact hnab hp2 hq hz hBelow hD hex hp1
  have S : RouteDSetup p f K z := mk_routeDSetup hp2 hq hz hBelow hconn hex hp1
  rcases exists_shape_or_multi S.ih (mem_conjClass_self K) hz
    (singleton_not_subset_center hnab hz.ne_one) with ⟨a, t, n, hsh⟩ | hm
  · exact hshape a t n G hnab K z S hsh
  · exact hmulti G hnab K z S hm

theorem coreStep_small_of_noDataBootD (hs4 : CITSectionalFour) (hd : SmallDisconnected p f)
    (hN : NoDataBootD p f) (hshape : ∀ (a : ℕ) (t : StatedLieTag) (n : ℕ), ShapePiece p f a t n)
    (hmulti : MultiPiece p f) (hup : SmallUpgrade p f) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z)
    (hBelow : CITBelowU p f (Nat.card G)) (h3 : 3 ≤ CFSG.Open.twoRank G)
    (hgen : ¬ (RouteD.DeltaConnected (𝒞 K) ∧ BootData p f (𝒞 K))) :
    LieSystem p f G (𝒞 K) := by
  by_cases h4 : TwoSubgroupsFourGenerated G
  · exact hup G hnab hp2 hq K z hz
      (hs4 G hnab z hz.orderOf_eq_two K hz.mem hz.subnormal
        (witness_of_isClassicalMember hp2 hq hz) (not_isSolvable_of_isClassicalMember hz) ⟨h3, h4⟩)
  · by_cases hΔ : CFSG.ClassicalInvolution.DeltaConnected K
    · have hB : ¬ BootData p f (𝒞 K) := fun hB => hgen ⟨(deltaConnected_iff K).mp hΔ, hB⟩
      exact lieSystem_of_noDataBootD hN hshape hmulti hnab hp2 hq hz hBelow h3 h4
        (dConnected_of_deltaConnected hΔ) hB
    · exact hup G hnab hp2 hq K z hz (hd G hnab hp2 hq hBelow K z hz h3 h4 hΔ)

theorem dBridge_of_noDataBootD (hmodel : Balance.Bootstrap.LayerGenerationHybrid p)
    (hMFC : ModelFacts.CommutingFundamentalFactsFive p) (hexotic : ExoticLeviBlock p f)
    (hBN : BootNoTripleD p f) (hN : NoDataBootD p f) : DBridge p f :=
  deltaConnected_of_dConnected hmodel hMFC hexotic hBN (noDataD_of_noDataBootD hN)

end CFSG.ClassicalInvolution.SmallConn
