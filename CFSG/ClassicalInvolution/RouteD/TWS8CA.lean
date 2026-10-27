module

public import CFSG.ClassicalInvolution.RouteD.TWS8Trans
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

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

local notation "LTag" => CFSG.Assembly.LowTwoRank.StatedLieTag

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.RouteD.TWS8

section Statement

variable (p f : ℕ) [Fact p.Prime]


@[expose] def TwinPairMax (tY : LTag) (nY : ℕ) : Prop :=
  ∀ (R R' : Subgroup (modelUniv tY nY p f Fact.out).K) (x x' : (modelUniv tY nY p f Fact.out).K),
    TwinDatum p f tY nY R R' x x' →
      IsCoatom (G2D4Models.conjStabilizer
        ({R, R'} : Set (Subgroup (modelUniv tY nY p f Fact.out).K)))

end Statement

section CA

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K T : Subgroup G} {z : G} {tY : LTag} {nY : ℕ}


theorem ca_of_twinPairMax (hnab : ∃ x y : G, x * y ≠ y * x) (S : RouteDSetup p f K z)
    (hrow : TwinRow tY nY) (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z)
    (hT : IsTwinAt (𝒞 K) K T z) (clsT : IsClassicalMember p f T z)
    (hMax : TwinPairMax p f tY nY) {N : Subgroup G} (hNΩ : N ∈ 𝒞 K)
    (hNΦ : ∀ L ∈ phi K T z, Commutes N L) : N = K ∨ N = T := by
  classical
  have hKΩ : K ∈ 𝒞 K := CoreAssembly.mem_conjClass_self K
  have hKiso : ∀ L ∈ centralizingMembers (𝒞 K) {z}, L ≠ K → Commutes K L :=
    fun L hL hLK => hT.comm_K L hL hLK
  have hTiso : ∀ L ∈ centralizingMembers (𝒞 K) {z}, L ≠ T → Commutes T L :=
    fun L hL hLT => hT.comm_T L hL hLT
  obtain ⟨hG2, hD4, hnA1⟩ := hrow.tag_facts
  have rf := LocalShapeT.twinRowFacts hshape S.odd S.five hG2 hD4 hnA1
  obtain ⟨d⟩ := LocalShapeT.nonempty_dictT2 hD4 rf.fsc S.inClass hKΩ S.cls hshape
  obtain ⟨J, hJ, hJK, hJT⟩ := exists_big_member S.inClass S.p1 rf d hKiso hTiso
  obtain ⟨t, hJt⟩ := S.inClass.classical J hJ.1
  have htz : t ≠ z := involution_ne_of_member hnab S hrow hshape hT hJ hJK hJT hJt
  obtain ⟨A⟩ := exists_atT S hrow hshape hT clsT hJ hJK hJT hJt htz
  have hJΦ : J ∈ phi K T z := ⟨hJ, hJK, hJT⟩
  have hJ₂Φ : A.J₂ ∈ phi K T z := ⟨A.hJ₂z, A.hJ₂K, A.hJ₂T⟩
  have hNΩt : N ∈ centralizingMembers (𝒞 K) {t} := ⟨hNΩ, fun n hn => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hNΦ J hJΦ n hn t hJt.mem⟩
  have hNJ : N ≠ J := fun h => not_commutes_self_of_mem S.inClass hJ.1 (by
    have := hNΦ J hJΦ
    rwa [h] at this)
  have hNJ₂ : N ≠ A.J₂ := fun h => not_commutes_self_of_mem S.inClass A.hJ₂t.1 (by
    have := hNΦ A.J₂ hJ₂Φ
    rwa [h] at this)
  obtain ⟨y, hy, hyKN, hyψ⟩ := link_big' S.inClass S.exact A.hP1 A.rf A.d (K := J) (T := A.J₂)
    (L := K) (L' := N) A.hJt A.hJ₂t A.hJ₂J.symm A.hJiso A.hJ₂iso A.hKt hJK.symm A.hJ₂K.symm
    hNΩt hNJ hNJ₂
  have hyN : y ∈ normX K T z := mem_normX_iff.mpr
    (conjSub_xGen_eq S hrow hshape hT y (fun L hL => by
      rw [hyKN]
      exact hNΦ L hL))
  have hMaxA := hMax A.RK A.RT A.x A.x' A.hdat
  have hN : ∀ y' ∈ locLayer (𝒞 K) t, (conjSub y' K = K ∨ conjSub y' K = T) →
      y' ∈ normX K T z := by
    intro y' _ h
    refine mem_normX_iff.mpr (conjSub_xGen_eq S hrow hshape hT y' (fun L hL => ?_))
    rcases h with h | h
    · rw [h]
      exact hT.comm_K L hL.1 hL.2.1
    · rw [h]
      exact hT.comm_T L hL.1 hL.2.2
  rcases transfer_max S A hMaxA (normX K T z) hN with hall | hone
  · exact (false_of_normalizes hnab S hrow hshape hT hJ hJK hJT hJt A hall).elim
  · have := hone y hyN hy hyψ
    rw [hyKN] at this
    exact this

end CA

section NC

variable {p f : ℕ} [Fact p.Prime] {P : LTag → ℕ → Prop}


theorem twinYNoCentralOn_of_twinPairMax
    (hMax : ∀ tY nY, P tY nY → TwinPairMax p f tY nY) : TwinYNoCentralOn p f P := by
  classical
  intro G _ _ _ hnab K z S tY nY hrow hP hshape T hT clsT e M hM
  by_contra hcon
  have hcomm : ∀ N ∈ phi K T z, Commutes M N := by
    intro N hN
    by_contra hnc
    exact hcon ⟨N, hN.1, hN.2.1, hN.2.2, hnc⟩
  have hodd : Odd (Nat.card (GaloisField p f)) := odd_natCard_galoisField S.odd S.five
  have hKT : Commutes K T := hT.comm_K T hT.mem hT.ne
  have hKΩ : K ∈ 𝒞 K := CoreAssembly.mem_conjClass_self K
  rcases ca_of_twinPairMax hnab S hrow hshape hT clsT (hMax tY nY hP) hM.1 hcomm with h | h
  · subst h
    exact e.not_mem_centralizingMembers_left S.cls (S.exact _ hKΩ) hodd hKT hM
  · subst h
    exact e.not_mem_centralizingMembers_right clsT (S.exact _ hT.mem.1) hodd hKT hM

theorem twinYNoCentralOn_odd3_of_twinPairMax (hMax : TwinPairMax p f .POmegaOdd 3) :
    TwinYNoCentralOn p f fun t n => t = .POmegaOdd ∧ n = 3 :=
  twinYNoCentralOn_of_twinPairMax fun _ _ hl => by
    obtain ⟨rfl, rfl⟩ := hl
    exact hMax

theorem twinYNoCentralOn_minus4_of_twinPairMax (hMax : TwinPairMax p f .POmegaMinus 4) :
    TwinYNoCentralOn p f fun t n => t = .POmegaMinus ∧ n = 4 :=
  twinYNoCentralOn_of_twinPairMax fun _ _ hl => by
    obtain ⟨rfl, rfl⟩ := hl
    exact hMax

end NC

end CFSG.ClassicalInvolution.RouteD.TWS8
