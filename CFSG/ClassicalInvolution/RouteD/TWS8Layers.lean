module

public import CFSG.ClassicalInvolution.RouteD.TWS8Count
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

namespace CFSG.ClassicalInvolution.RouteD.TWS8

section Layers

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K T : Subgroup G} {z : G} {tY : StatedLieTag} {nY : ℕ}


theorem eq_top_of_layers (S : RouteDSetup p f K z) (hrow : TwinRow tY nY)
    (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z) (hT : IsTwinAt (𝒞 K) K T z)
    {J : Subgroup G} {t : G} (hJ : J ∈ centralizingMembers (𝒞 K) {z}) (hJK : J ≠ K)
    (hJT : J ≠ T) (hJt : IsClassicalMember p f J t) (A : AtT p f K T J z t tY nY)
    {H : Subgroup G} (hYz : centralizingLayer (𝒞 K) {z} ≤ H)
    (hYt : centralizingLayer (𝒞 K) {t} ≤ H) : H = ⊤ := by
  classical
  have hKΩ : K ∈ 𝒞 K := CoreAssembly.mem_conjClass_self K
  have hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  obtain ⟨hG2, hD4, hnA1⟩ := hrow.tag_facts
  have rf := LocalShapeT.twinRowFacts hshape S.odd S.five hG2 hD4 hnA1
  obtain ⟨d⟩ := LocalShapeT.nonempty_dictT2 hD4 rf.fsc S.inClass hKΩ S.cls hshape
  have hKz : K ∈ centralizingMembers (𝒞 K) {z} :=
    ⟨hKΩ, le_centralizer_of_isClassicalMember S.cls⟩
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
  exact TWZ.eq_top_of_closure S.inClass S.conn hKΩ hKH hJH hneighK hneighJ

theorem false_of_normalizes (hnab : ∃ x y : G, x * y ≠ y * x) (S : RouteDSetup p f K z)
    (hrow : TwinRow tY nY) (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z)
    (hT : IsTwinAt (𝒞 K) K T z) {J : Subgroup G} {t : G}
    (hJ : J ∈ centralizingMembers (𝒞 K) {z}) (hJK : J ≠ K) (hJT : J ≠ T)
    (hJt : IsClassicalMember p f J t) (A : AtT p f K T J z t tY nY)
    (h : ∀ N ∈ centralizingMembers (𝒞 K) {t}, N ≠ J → N ≠ A.J₂ →
      N ≤ normX K T z) : False := by
  classical
  have hcen : Subgroup.center G = ⊥ := CoreAssembly.center_eq_bot hnab
  have hJΦ : J ∈ phi K T z := ⟨hJ, hJK, hJT⟩
  have hJ₂Φ : A.J₂ ∈ phi K T z := ⟨A.hJ₂z, A.hJ₂K, A.hJ₂T⟩
  have hΦX : ∀ N ∈ phi K T z, N ≤ normX K T z := fun N hN =>
    ((le_iSup₂ (f := fun (N : Subgroup G) (_ : N ∈ phi K T z) => N) N hN).trans
      (Subgroup.le_normalizer : xGen K T z ≤ normX K T z))
  have hYz : centralizingLayer (𝒞 K) {z} ≤ normX K T z := by
    refine iSup₂_le fun N hN => ?_
    by_cases hNK : N = K
    · subst hNK
      exact h _ A.hKt hJK.symm A.hJ₂K.symm
    by_cases hNT : N = T
    · subst hNT
      exact h _ A.hTt hJT.symm A.hJ₂T.symm
    exact hΦX N ⟨hN, hNK, hNT⟩
  have hYt : centralizingLayer (𝒞 K) {t} ≤ normX K T z := by
    refine iSup₂_le fun N hN => ?_
    by_cases hNJ : N = J
    · subst hNJ
      exact hΦX _ hJΦ
    by_cases hNJ₂ : N = A.J₂
    · subst hNJ₂
      exact hΦX _ hJ₂Φ
    exact h N hN hNJ hNJ₂
  have htop := eq_top_of_layers S hrow hshape hT hJ hJK hJT hJt A hYz hYt
  have htop' : Subgroup.normalizer (xGen K T z : Set G) = ⊤ := htop
  have hnorm : (xGen K T z).Normal := Subgroup.normalizer_eq_top_iff.mp htop'
  have hKX : ∀ N ∈ phi K T z, Commutes K N := fun N hN => hT.comm_K N hN.1 hN.2.1
  have := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (xGen K T z) with hbot | hX
  · have hJle : J ≤ xGen K T z :=
      le_iSup₂ (f := fun (N : Subgroup G) (_ : N ∈ phi K T z) => N) J hJΦ
    rw [hbot] at hJle
    have := Subgroup.mem_bot.mp (hJle hJt.mem)
    exact ne_one_of_orderOf_eq_two hJt.orderOf_eq_two this
  · have hKc : K ≤ Subgroup.center G := by
      intro k hk
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ xGen K T z := by rw [hX]; trivial
      have hXle : xGen K T z ≤ Subgroup.centralizer (K : Set G) := by
        refine iSup₂_le fun N hN => ?_
        intro n hn
        rw [Subgroup.mem_centralizer_iff]
        intro k' hk'
        exact hKX N hN k' hk' n hn
      have := Subgroup.mem_centralizer_iff.mp (hXle hg) k hk
      exact this.symm
    rw [hcen] at hKc
    have := Subgroup.mem_bot.mp (hKc S.cls.mem)
    exact ne_one_of_orderOf_eq_two S.cls.orderOf_eq_two this

end Layers

end CFSG.ClassicalInvolution.RouteD.TWS8
