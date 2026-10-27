module

public import Mathlib
public import CFSG.ClassicalInvolution.SmallCases.SmallConnSetup
public import CFSG.ClassicalInvolution.PerfectCase.Basic
public import CFSG.ClassicalInvolution.Balance.BootstrapLevi
public import CFSG.ClassicalInvolution.Balance.PassTwoWeak
public import CFSG.ClassicalInvolution.Asc77.WP3Fuzzy
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

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ComponentClassification

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem oddCore_le_centralizer_of_localOddCentral {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}
    (hK : K ∈ Ω) (hz : IsClassicalMember p f K z) (hP1 : LocalOddCentral Ω {z}) :
    oddCoreIn K ≤ Subgroup.centralizer (K : Set G) := by
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, isSubnormal_le hz.subnormal⟩
  have hKY : K ≤ centralizingLayer Ω {z} := le_centralizingLayer hKz
  have hsub : IsSubnormal K (centralizingLayer Ω {z}) := by
    have h := isSubnormal_inf hz.subnormal (centralizingLayer Ω {z})
    rwa [inf_eq_left.mpr hKY, inf_eq_right.mpr (centralizingLayer_le_centralizer Ω {z})] at h
  have hO := oddCoreIn_le_of_isSubnormal hsub
  intro o ho
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  obtain ⟨y, hy, hyo⟩ := hO ho
  have hyc : y ∈ Subgroup.center ↥(centralizingLayer Ω {z}) := hP1 hy
  have hcomm := Subgroup.mem_center_iff.mp hyc ⟨k, hKY hk⟩
  have hval : k * (y : G) = (y : G) * k := congrArg Subtype.val hcomm
  rw [← hyo]
  exact hval

theorem isQuasisimple_of_localOddCentral (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)} {K : Subgroup G}
    {z : G} (hK : K ∈ Ω) (hz : IsClassicalMember p f K z) (hP1 : LocalOddCentral Ω {z}) :
    CFSG.Open.IsQuasisimple K := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [GaloisField.card p f hf]
    omega
  obtain ⟨e⟩ := hz.nonempty_equiv
  have hKq : CFSG.Open.IsQuasisimple (K ⧸ componentClassificationOddCore K) :=
    Components.quasisimple_of_equiv e (CFSG.ClassicalInvolution.isQuasisimple_specialLinearGroup_two
      h4)
  have hc := oddCore_le_centralizer_of_localOddCentral hK hz hP1
  have : Group.IsPerfect K := hz.perfect
  refine CentralExtensions.quasisimple_of_surjective hKq (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) ?_
  rw [QuotientGroup.ker_mk']
  intro o ho
  rw [Subgroup.mem_center_iff]
  intro k
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hc ⟨o, ho, rfl⟩) k k.2)

theorem exactMembers_of_localOddCentral_ne_nine (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {K : Subgroup G} {z : G}
    (hK : K ∈ Ω) (hz : IsClassicalMember p f K z) (hP1 : LocalOddCentral Ω {z}) :
    ExactMembers Ω := by
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  exact exactMembers_of_isQuasisimple hp2 hf h9 hΩ hsingle hK
    (isQuasisimple_of_localOddCentral hq hK hz hP1)

variable [IsSimpleGroup G]

theorem routeD_deltaConnected_of_dConnected_of_p1 (hnab : ∃ x y : G, x * y ≠ y * x)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z)
    (hBelow : CITBelowU p f (Nat.card G)) (hD : DConnected (𝒞 K))
    (hP1 : LocalOddCentral (𝒞 K) {z}) : RouteD.DeltaConnected (𝒞 K) := by
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  have hΩ : InClass p f (𝒞 K) := inClass_conjugates hz
  have hIH := localLieSystems_of_citBelowU hΩ hBelow
  have hP1all := localOddCentral_of_classicalMember hp2 hf hΩ (exists_single_class K)
    (mem_conjClass_self K) hz hP1
  have hqs : ∀ J ∈ 𝒞 K, CFSG.Open.IsQuasisimple J := fun J hJ => by
    obtain ⟨w, hw⟩ := hΩ.classical J hJ
    exact isQuasisimple_of_localOddCentral hq hJ hw (hP1all J hJ w hw)
  exact routeD_deltaConnected_of_omegaConnected ⟨K, mem_conjClass_self K⟩
    (omegaConnected_of_tqChain hnab hΩ hIH hqs hP1all (tqChain_of_dConnected hp2 hq hz hD))

theorem exactMembers_of_localOddCentral (hexotic : ExoticLeviBlock p f)
    (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G}
    (hz : IsClassicalMember p f K z) (hBelow : CITBelowU p f (Nat.card G))
    (hD : DConnected (𝒞 K)) (hP1 : LocalOddCentral (𝒞 K) {z}) : ExactMembers (𝒞 K) := by
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  have hΩ : InClass p f (𝒞 K) := inClass_conjugates hz
  have hsingle := exists_single_class K
  have hKΩ : K ∈ 𝒞 K := mem_conjClass_self K
  by_cases h9 : p ^ f = 9
  · have hconn : DeltaClosure.OmegaConnected (𝒞 K) :=
      BootRank3.omegaConnected_of_routeD
        (routeD_deltaConnected_of_dConnected_of_p1 hnab hp2 hq hz hBelow hD hP1)
    have hIH := localLieSystems_of_citBelowU hΩ hBelow
    have hP1all := localOddCentral_of_classicalMember hp2 hf hΩ hsingle hKΩ hz hP1
    exact exactMembers_of_connected_nine hnab hp2 hq h9 hΩ hsingle hIH hconn hP1all hexotic
  · exact exactMembers_of_localOddCentral_ne_nine hp2 hq h9 hΩ hsingle hKΩ hz hP1

section Statements

omit [Finite G] [IsSimpleGroup G] in
@[expose] def NoDataP1D (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → 3 ≤ CFSG.Open.twoRank G → ¬ TwoSubgroupsFourGenerated G →
      DConnected (𝒞 K) → ¬ BootData p f (𝒞 K) → LocalOddCentral (𝒞 K) {z}

theorem noDataBootD_of_noDataP1D (hexotic : ExoticLeviBlock p f) (h : NoDataP1D p f) :
    NoDataBootD p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow h3 h4 hD hB
  have hP1 := h G hnab hp2 hq K z hz hBelow h3 h4 hD hB
  exact ⟨exactMembers_of_localOddCentral hexotic hnab hp2 hq hz hBelow hD hP1, hP1⟩

theorem noDataP1D_of_noDataBootD (h : NoDataBootD p f) : NoDataP1D p f :=
  fun G _ _ _ hnab hp2 hq K z hz hBelow h3 h4 hD hB =>
    (h G hnab hp2 hq K z hz hBelow h3 h4 hD hB).2

omit [Finite G] [IsSimpleGroup G] in
@[expose] def BootNoTripleP1D (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → DConnected (𝒞 K) → BootData p f (𝒞 K) →
      ¬ IndepTriple p f (𝒞 K) → LocalOddCentral (𝒞 K) {z}

theorem bootNoTripleD_of_bootNoTripleP1D (hexotic : ExoticLeviBlock p f)
    (h : BootNoTripleP1D p f) : BootNoTripleD p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hD hdata hT
  have hP1 := h G hnab hp2 hq K z hz hBelow hD hdata hT
  exact ⟨exactMembers_of_localOddCentral hexotic hnab hp2 hq hz hBelow hD hP1, hP1⟩

omit [Finite G] [IsSimpleGroup G] in
@[expose] def ConnectedP1D (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → CITBelowU p f (Nat.card G) → ∀ (K : Subgroup G) (z : G),
      IsClassicalMember p f K z → 3 ≤ CFSG.Open.twoRank G → ¬ TwoSubgroupsFourGenerated G →
      DConnected (𝒞 K) → LocalOddCentral (𝒞 K) {z}

theorem exactP1D_of_connectedP1D (hexotic : ExoticLeviBlock p f) (h : ConnectedP1D p f) :
    ExactP1D p f := by
  intro G _ _ _ hnab hp2 hq hBelow K z hz h3 h4 hD
  have hP1 := h G hnab hp2 hq hBelow K z hz h3 h4 hD
  exact ⟨exactMembers_of_localOddCentral hexotic hnab hp2 hq hz hBelow hD hP1, hP1⟩

theorem dBridge_of_connectedP1D (h : ConnectedP1D p f) : DBridge p f := by
  intro G _ _ _ hnab hp2 hq hBelow K z hz h3 h4 hD
  exact (deltaConnected_iff K).mpr
    (routeD_deltaConnected_of_dConnected_of_p1 hnab hp2 hq hz hBelow hD
      (h G hnab hp2 hq hBelow K z hz h3 h4 hD))

theorem connectedP1D_of_cases (hmodel : LayerGenerationHybrid p)
    (hMFC : ModelFacts.CommutingFundamentalFactsFive p) (hexotic : ExoticLeviBlock p f)
    (hBN : BootNoTripleP1D p f) (hN : NoDataP1D p f) : ConnectedP1D p f := by
  intro G _ _ _ hnab hp2 hq hBelow K z hz h3 h4 hD
  by_cases hT : IndepTriple p f (𝒞 K)
  · exact (bootTripleD hmodel hMFC hexotic G hnab hp2 hq K z hz hBelow hD hT).2
  · by_cases hdata : BootData p f (𝒞 K)
    · exact hBN G hnab hp2 hq K z hz hBelow hD hdata hT
    · exact hN G hnab hp2 hq K z hz hBelow h3 h4 hD hdata

end Statements

end CFSG.ClassicalInvolution.SmallConn
