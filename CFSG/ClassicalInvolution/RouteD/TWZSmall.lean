module

public import CFSG.ClassicalInvolution.RouteD.TWZOuter
public import CFSG.ClassicalInvolution.RouteD.TWZGlobal
public import CFSG.ClassicalInvolution.RouteD.TWYSp2
public import CFSG.ClassicalInvolution.RouteD.TWZLinkSp2
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

section Small

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K T : Subgroup G} {z : G} {tY : StatedLieTag} {nY : ℕ}


theorem false_of_small_component (hnab : ∃ x y : G, x * y ≠ y * x)
    (S : RouteDSetup p f K z) (hrow : TwinRow tY nY)
    (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z) (hT : IsTwinAt (𝒞 K) K T z)
    (clsT : IsClassicalMember p f T z) (e : TwinElt K T z) (hMF : TwinMFGeneration p f tY nY)
    (hP1 : LocalOddCentral (𝒞 K) {e.u})
    (D : LieSystemData p f (locQuot (𝒞 K) e.u) (locFamily (𝒞 K) e.u)) (hcard : D.card = 1)
    (i : Fin D.card)
    (hsmall : (D.tag i = .PSp ∧ D.rank i = 2) ∨ (D.tag i = .PSL ∧ D.rank i = 4) ∨
      (D.tag i = .PSU ∧ D.rank i = 4)) : False := by
  classical
  have hKΩ : K ∈ 𝒞 K := CoreAssembly.mem_conjClass_self K
  have hKT' : Commutes K T := hT.comm_K T hT.mem hT.ne
  have hz2 : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two S.cls.orderOf_eq_two
  have hKz : K ∈ centralizingMembers (𝒞 K) {z} :=
    ⟨hKΩ, le_centralizer_of_isClassicalMember S.cls⟩
  have hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  have hncs : ∀ L ∈ 𝒞 K, ¬ Commutes L L := fun L hL => not_commutes_self_of_mem S.inClass hL
  obtain ⟨hG2, hD4, hnA1⟩ := hrow.tag_facts
  have rf := LocalShapeT.twinRowFacts hshape S.odd S.five hG2 hD4 hnA1
  obtain ⟨d⟩ := LocalShapeT.nonempty_dictT2 hD4 rf.fsc S.inClass hKΩ S.cls hshape
  obtain ⟨J, -, t, hJ, hJK, hJT, hJt, htz, -, -, -⟩ :=
    exists_frameMembers hnab S hrow hshape hT clsT e
  obtain ⟨J₂, hJ₂t, hJ₂J, hJ₂cls, hJ₂K, hJ₂T, hJiso, -⟩ :=
    exists_twin_iso_at_t S hT.ne.symm hT.mem hKiso hTiso clsT hJ hJK hJT hJt htz
  have hJ₂z : J₂ ∈ centralizingMembers (𝒞 K) {z} :=
    ⟨hJ₂t.1, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
      (hJ₂K.symm z S.cls.mem y hy).symm⟩
  have hJ₂K' : J₂ ≠ K := fun h => hncs K hKΩ (by rw [h] at hJ₂K; exact hJ₂K)
  have hJ₂T' : J₂ ≠ T := fun h => hncs T hT.mem.1 (by rw [h] at hJ₂T; exact hJ₂T)
  have hΦu : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → N ≠ T →
      N ∈ centralizingMembers (𝒞 K) {e.u} := fun N hN hNK hNT =>
    e.mem_centralizingMembers_u hN.1 (hKiso N hN hNK).symm (hTiso N hN hNT).symm
  have hJu : J ∈ centralizingMembers (𝒞 K) {e.u} := hΦu J hJ hJK hJT
  have hJ₂u : J₂ ∈ centralizingMembers (𝒞 K) {e.u} := hΦu J₂ hJ₂z hJ₂K' hJ₂T'
  have hJJ₂ : Commutes J J₂ := hJiso J₂ hJ₂t hJ₂J
  have hac : e.a * e.u = e.u * e.a := by
    have hc : e.a * e.a' = e.a' * e.a := hKT' _ e.mem_a _ e.mem_a'
    unfold TwinElt.u
    calc e.a * (e.a * e.a') = e.a * (e.a' * e.a) := by rw [hc]
      _ = (e.a * e.a') * e.a := by group
  have hc4 : e.a * e.a * (e.a * e.a) = 1 := by rw [e.mul_self_a, hz2]
  have hcJ : ∀ j ∈ J, e.a * j = j * e.a := fun j hj => hKiso J hJ hJK e.a e.mem_a j hj
  have hcJ₂ : ∀ j ∈ J₂, e.a * j = j * e.a := fun j hj => hJ₂K j hj e.a e.mem_a |>.symm
  have hsmall' : (D.tag i = .PSp ∧ D.rank i = 2) ∨ (D.tag i = .PSL ∧ D.rank i = 4) ∨
      (D.tag i = .PSU ∧ D.rank i = 4) := hsmall
  rcases actX_sq_dichotomy S.odd S.five S.inClass S.exact hP1 D hcard i hsmall' hJu hJ₂u
      hJ₂J.symm hJJ₂ hJt hJ₂cls hac hc4 hcJ hcJ₂ with hZ | hZt
  ·
    refine false_of_layer_le_centralizer hnab S hrow hshape hT clsT e hMF fun N hN => ?_
    have := hZ N hN
    rwa [e.mul_self_a] at this
  ·
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
    rw [e.mul_self_a] at hzt
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

end Small

section Residual

variable (p f : ℕ) [Fact p.Prime]

@[expose] def TwinYSp2NoMinus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → LocalShapeT p f 2 .PSp 2 (𝒞 K) z →
      ∀ T : Subgroup G, IsTwinAt (𝒞 K) K T z → IsClassicalMember p f T z →
        ∀ e : TwinElt K T z, LocalOddCentral (𝒞 K) {e.u} →
          ∀ D : LieSystemData p f (locQuot (𝒞 K) e.u) (locFamily (𝒞 K) e.u), D.card = 1 →
            ∀ i : Fin D.card, (D.tag i = .POmegaMinus ∧ D.rank i = 4) → False

end Residual

section Reduce

variable (p f : ℕ) [Fact p.Prime]


theorem twinYSp2Small_of_noMinus (h : TwinYSp2NoMinus p f) : TWY.TwinYSp2Small p f := by
  intro G _ _ _ hnab K z S hshape T hT clsT e hP1 D hcard i hsmall
  have hrow : TwinRow .PSp 2 := Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
  have hMF : TwinMFGeneration p f .PSp 2 := twinMFGeneration_psp2 S.odd (le_trans (by norm_num : 3 ≤ 5) S.five)
  rcases hsmall with h1 | h2 | h3 | h4
  · exact false_of_small_component hnab S hrow hshape hT clsT e hMF hP1 D hcard i (Or.inl h1)
  · exact false_of_small_component hnab S hrow hshape hT clsT e hMF hP1 D hcard i
      (Or.inr (Or.inl h2))
  · exact false_of_small_component hnab S hrow hshape hT clsT e hMF hP1 D hcard i
      (Or.inr (Or.inr h3))
  · exact h G hnab K z S hshape T hT clsT e hP1 D hcard i h4

theorem twinYRankOn_psp2_of_noMinus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩall : HypOmegaModAll p f)
    (hAE : AEmptyTwinExact p f) (hcls : TwinInvolution p f) (hP4 : Ih8G2D4 p f)
    (hH : TwinFrameHyp51 p f) (h : TwinYSp2NoMinus p f) :
    TwinYRankOn p f fun t n => t = .PSp ∧ n = 2 :=
  TWY.twinYRankOn_psp2_of_small hp2 hq hΩall hAE hcls hP4 hH (twinYSp2Small_of_noMinus p f h)

theorem twinSp2Linked_of_noMinus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩall : HypOmegaModAll p f)
    (hAE : AEmptyTwinExact p f) (hcls : TwinInvolution p f) (hP4 : Ih8G2D4 p f)
    (hH : TwinFrameHyp51 p f) (h : TwinYSp2NoMinus p f) : TwinSp2Linked p f :=
  TWS.twinSp2Linked_of_residuals hp2 hq hΩall hAE hcls hP4 hH
    (twinYRankOn_psp2_of_noMinus p f hp2 hq hΩall hAE hcls hP4 hH h) (twinYLinkedSp2 p f)

end Reduce

end CFSG.ClassicalInvolution.RouteD.TWZ
