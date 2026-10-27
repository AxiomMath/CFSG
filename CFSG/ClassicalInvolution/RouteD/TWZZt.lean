module

public import CFSG.ClassicalInvolution.RouteD.TWZGlobal
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

namespace CFSG.ClassicalInvolution.RouteD.TWZ

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

set_option linter.unusedSectionVars false

section Zt

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K T : Subgroup G} {z : G} {tY : StatedLieTag} {nY : ℕ}


theorem exists_twin_frame (hnab : ∃ x y : G, x * y ≠ y * x) (S : RouteDSetup p f K z)
    (hrow : TwinRow tY nY) (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z)
    (hT : IsTwinAt (𝒞 K) K T z) (clsT : IsClassicalMember p f T z) (e : TwinElt K T z) :
    ∃ (J J₂ : Subgroup G) (t : G), J ∈ centralizingMembers (𝒞 K) {z} ∧ J ≠ K ∧ J ≠ T ∧
      IsClassicalMember p f J t ∧ t ≠ z ∧ J₂ ∈ centralizingMembers (𝒞 K) {t} ∧ J₂ ≠ J ∧
      IsClassicalMember p f J₂ t ∧ Commutes J₂ K ∧ Commutes J₂ T ∧
      (∀ L ∈ centralizingMembers (𝒞 K) {t}, L ≠ J → Commutes J L) := by
  have hKΩ : K ∈ 𝒞 K := CoreAssembly.mem_conjClass_self K
  have hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  obtain ⟨J, -, t, hJ, hJK, hJT, hJt, htz, -, -, -⟩ :=
    exists_frameMembers hnab S hrow hshape hT clsT e
  obtain ⟨J₂, hJ₂t, hJ₂J, hJ₂cls, hJ₂K, hJ₂T, hJiso, -⟩ :=
    exists_twin_iso_at_t S hT.ne.symm hT.mem hKiso hTiso clsT hJ hJK hJT hJt htz
  exact ⟨J, J₂, t, hJ, hJK, hJT, hJt, htz, hJ₂t, hJ₂J, hJ₂cls, hJ₂K, hJ₂T, hJiso⟩

theorem false_of_layer_le_centralizer_tz (S : RouteDSetup p f K z) (hrow : TwinRow tY nY)
    (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z) (hT : IsTwinAt (𝒞 K) K T z)
    (e : TwinElt K T z) {J : Subgroup G} {t : G} (hJ : J ∈ centralizingMembers (𝒞 K) {z})
    (hJK : J ≠ K) (hJT : J ≠ T)
    (hJiso : ∀ L ∈ centralizingMembers (𝒞 K) {t}, L ≠ J → Commutes J L)
    (hZt : ∀ N ∈ centralizingMembers (𝒞 K) {e.u}, N ≤ Subgroup.centralizer ({t * z} : Set G)) :
    False := by
  have hKΩ : K ∈ 𝒞 K := CoreAssembly.mem_conjClass_self K
  have hz2 : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two S.cls.orderOf_eq_two
  have hKz : K ∈ centralizingMembers (𝒞 K) {z} :=
    ⟨hKΩ, le_centralizer_of_isClassicalMember S.cls⟩
  have hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  obtain ⟨hG2, hD4, hnA1⟩ := hrow.tag_facts
  have rf := LocalShapeT.twinRowFacts hshape S.odd S.five hG2 hD4 hnA1
  obtain ⟨d⟩ := LocalShapeT.nonempty_dictT2 hD4 rf.fsc S.inClass hKΩ S.cls hshape
  have hΦu : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → N ≠ T →
      N ∈ centralizingMembers (𝒞 K) {e.u} := fun N hN hNK hNT =>
    e.mem_centralizingMembers_u hN.1 (hKiso N hN hNK).symm (hTiso N hN hNT).symm
  obtain ⟨L', hL', hL'J, hnc⟩ := exists_noncomm_of_ne S.inClass S.exact S.p1 rf d hKz hT.mem
    hT.ne.symm hKiso hTiso hJ hJK hJT
  refine hnc ?_
  by_cases hL'K : L' = K
  · rw [hL'K]
    exact (hKiso J hJ hJK).symm
  by_cases hL'T : L' = T
  · rw [hL'T]
    exact (hTiso J hJ hJT).symm
  have hL'u : L' ∈ centralizingMembers (𝒞 K) {e.u} := hΦu L' hL' hL'K hL'T
  have hzt := hZt L' hL'u
  have hL't : L' ∈ centralizingMembers (𝒞 K) {t} := by
    refine ⟨hL'.1, fun l hl => ?_⟩
    have h1 : l * z = z * l := Subgroup.mem_centralizer_singleton_iff.mp (hL'.2 hl)
    have h2 : l * (t * z) = (t * z) * l := Subgroup.mem_centralizer_singleton_iff.mp (hzt hl)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc l * t = l * t * (z * z) := by rw [hz2, mul_one]
      _ = l * (t * z) * z := by group
      _ = (t * z) * l * z := by rw [h2]
      _ = (t * z) * (l * z) := by group
      _ = (t * z) * (z * l) := by rw [h1]
      _ = t * (z * z) * l := by group
      _ = t * l := by rw [hz2, mul_one]
  exact hJiso L' hL't hL'J

end Zt

end CFSG.ClassicalInvolution.RouteD.TWZ
