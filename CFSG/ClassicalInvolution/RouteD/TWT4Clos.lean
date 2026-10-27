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

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.RouteD.TWT4

section Closure

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K T : Subgroup G} {z : G} {tY : StatedLieTag} {nY : ℕ}


theorem eq_one_of_centralizes_layers (hnab : ∃ x y : G, x * y ≠ y * x)
    (S : RouteDSetup p f K z) (hrow : TwinRow tY nY)
    (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z) (hT : IsTwinAt (𝒞 K) K T z)
    (clsT : IsClassicalMember p f T z) {J : Subgroup G} {t : G}
    (hJ : J ∈ centralizingMembers (𝒞 K) {z}) (hJK : J ≠ K) (hJT : J ≠ T)
    (hJt : IsClassicalMember p f J t) (s : G)
    (hsz : ∀ y ∈ centralizingLayer (𝒞 K) {z}, s * y = y * s)
    (hst : ∀ y ∈ centralizingLayer (𝒞 K) {t}, s * y = y * s) : s = 1 := by
  classical
  have hcen : Subgroup.center G = ⊥ := CoreAssembly.center_eq_bot hnab
  have hKΩ : K ∈ 𝒞 K := CoreAssembly.mem_conjClass_self K
  have hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  obtain ⟨hG2, hD4, hnA1⟩ := hrow.tag_facts
  have rf := LocalShapeT.twinRowFacts hshape S.odd S.five hG2 hD4 hnA1
  obtain ⟨d⟩ := LocalShapeT.nonempty_dictT2 hD4 rf.fsc S.inClass hKΩ S.cls hshape
  have htz : t ≠ z := involution_ne_of_member hnab S hrow hshape hT hJ hJK hJT hJt
  obtain ⟨A⟩ := exists_atT S hrow hshape hT clsT hJ hJK hJT hJt htz
  have hKz : K ∈ centralizingMembers (𝒞 K) {z} :=
    ⟨hKΩ, le_centralizer_of_isClassicalMember S.cls⟩
  set H : Subgroup G := Subgroup.centralizer ({s} : Set G) with hH
  have hYz : centralizingLayer (𝒞 K) {z} ≤ H := fun y hy => by
    rw [hH, Subgroup.mem_centralizer_singleton_iff]
    exact (hsz y hy).symm
  have hYt : centralizingLayer (𝒞 K) {t} ≤ H := fun y hy => by
    rw [hH, Subgroup.mem_centralizer_singleton_iff]
    exact (hst y hy).symm
  have hKH : K ≤ H := (le_centralizingLayer hKz).trans hYz
  have hJH : J ≤ H := (le_centralizingLayer hJ).trans hYz
  have hneighK : ∀ L ∈ 𝒞 K, L ≠ K → Commutes K L →
      ∃ y ∈ H, L = conjSub y K ∨ L = conjSub y J := by
    intro L hL hLK hc
    have hLz : L ∈ centralizingMembers (𝒞 K) {z} :=
      ⟨hL, fun l hl => Subgroup.mem_centralizer_singleton_iff.mpr (hc z S.cls.mem l hl).symm⟩
    by_cases hLT : L = T
    · have hLt : L ∈ centralizingMembers (𝒞 K) {t} := hLT ▸ A.hTt
      have hLJ : L ≠ J := by rw [hLT]; exact hJT.symm
      have hLJ₂ : L ≠ A.J₂ := by rw [hLT]; exact A.hJ₂T.symm
      obtain ⟨y, hy, hyeq⟩ := link_big S.inClass S.exact A.hP1 A.rf A.d (K := J) (T := A.J₂)
        (L := K) (L' := L) A.hJt A.hJ₂t A.hJ₂J.symm A.hJiso A.hJ₂iso A.hKt hJK.symm
        A.hJ₂K.symm hLt hLJ hLJ₂
      exact ⟨y, hYt hy, Or.inl hyeq.symm⟩
    · obtain ⟨y, hy, hyeq⟩ := link_big S.inClass S.exact S.p1 rf d hKz hT.mem hT.ne.symm hKiso
        hTiso (L := J) (L' := L) hJ hJK hJT hLz hLK hLT
      exact ⟨y, hYz hy, Or.inr hyeq.symm⟩
  have hneighJ : ∀ L ∈ 𝒞 K, L ≠ J → Commutes J L →
      ∃ y ∈ H, L = conjSub y K ∨ L = conjSub y J := by
    intro L hL hLJ hc
    have hLt : L ∈ centralizingMembers (𝒞 K) {t} :=
      ⟨hL, fun l hl => Subgroup.mem_centralizer_singleton_iff.mpr (hc t hJt.mem l hl).symm⟩
    by_cases hLJ₂ : L = A.J₂
    · obtain ⟨y, hy, hyeq⟩ := link_big S.inClass S.exact S.p1 rf d hKz hT.mem hT.ne.symm hKiso
        hTiso (L := J) (L' := L) hJ hJK hJT (hLJ₂ ▸ A.hJ₂z) (by rw [hLJ₂]; exact A.hJ₂K)
        (by rw [hLJ₂]; exact A.hJ₂T)
      exact ⟨y, hYz hy, Or.inr hyeq.symm⟩
    · obtain ⟨y, hy, hyeq⟩ := link_big S.inClass S.exact A.hP1 A.rf A.d (K := J) (T := A.J₂)
        (L := K) (L' := L) A.hJt A.hJ₂t A.hJ₂J.symm A.hJiso A.hJ₂iso A.hKt hJK.symm
        A.hJ₂K.symm hLt hLJ hLJ₂
      exact ⟨y, hYt hy, Or.inl hyeq.symm⟩
  have hHtop : H = ⊤ := TWZ.eq_top_of_closure S.inClass S.conn hKΩ hKH hJH hneighK hneighJ
  have hsc : s ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ H := by rw [hHtop]; trivial
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  rw [hcen, Subgroup.mem_bot] at hsc
  exact hsc

end Closure

end CFSG.ClassicalInvolution.RouteD.TWT4
