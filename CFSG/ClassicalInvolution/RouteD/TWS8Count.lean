module

public import CFSG.ClassicalInvolution.RouteD.TWT6B2
public import CFSG.ClassicalInvolution.RouteD.TWT4Clos
public import CFSG.ClassicalInvolution.ModelFacts.G2D4Block
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

section Defs

variable {G : Type} [Group G]

@[expose] def phi (K T : Subgroup G) (z : G) : Set (Subgroup G) :=
  {N | N ∈ centralizingMembers (𝒞 K) {z} ∧ N ≠ K ∧ N ≠ T}

@[expose] def xGen (K T : Subgroup G) (z : G) : Subgroup G :=
  ⨆ N ∈ phi K T z, N

@[expose] def normX (K T : Subgroup G) (z : G) : Subgroup G :=
  Subgroup.normalizer (xGen K T z : Set G)

theorem mem_normX_iff {K T : Subgroup G} {z g : G} :
    g ∈ normX K T z ↔ conjSub g (xGen K T z) = xGen K T z :=
  G2D4Models.normalizer_iff_conjSub_eq

theorem conjSub_iSup₂ (g : G) (s : Set (Subgroup G)) :
    conjSub g (⨆ N ∈ s, N) = ⨆ N ∈ conjSub g '' s, N := by
  rw [iSup_image]
  unfold conjSub
  rw [Subgroup.map_iSup]
  refine iSup_congr fun N => ?_
  rw [Subgroup.map_iSup]

end Defs

section Count

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K T : Subgroup G} {z : G}
  {tY : StatedLieTag} {nY : ℕ}


theorem conjSub_phi_eq (S : RouteDSetup p f K z) (hrow : TwinRow tY nY)
    (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z) (hT : IsTwinAt (𝒞 K) K T z) (g : G)
    (hg : ∀ N ∈ phi K T z, Commutes (conjSub g K) N) :
    conjSub g '' phi K T z = phi K T z := by
  classical
  have hKΩ : K ∈ 𝒞 K := CoreAssembly.mem_conjClass_self K
  have hKz : K ∈ centralizingMembers (𝒞 K) {z} :=
    ⟨hKΩ, le_centralizer_of_isClassicalMember S.cls⟩
  have hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  obtain ⟨hG2, hD4, hnA1⟩ := hrow.tag_facts
  have rf := LocalShapeT.twinRowFacts hshape S.odd S.five hG2 hD4 hnA1
  obtain ⟨d⟩ := LocalShapeT.nonempty_dictT2 hD4 rf.fsc S.inClass hKΩ S.cls hshape
  set M : Subgroup G := conjSub g K with hMdef
  set w : G := g * z * g⁻¹ with hw
  set TM : Subgroup G := conjSub g T with hTMdef
  have hMΩ : M ∈ 𝒞 K := S.inClass.conjInvariant g K hKΩ
  have hTM : IsTwinAt (𝒞 K) M TM w := TWT6.isTwinAt_conj S.inClass.conjInvariant hT g
  have hclsw : IsClassicalMember p f M w := S.cls.conj g
  have hMself : ¬ Commutes M M := not_commutes_self_of_mem S.inClass hMΩ
  have hΦw : ∀ N ∈ phi K T z, N ∈ centralizingMembers (𝒞 K) {w} ∧ N ≠ M := by
    intro N hN
    refine ⟨⟨hN.1.1, fun n hn => ?_⟩, fun hEq => hMself (hEq ▸ hg N hN)⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hg N hN w hclsw.mem n hn).symm
  have hΦsub : phi K T z ⊆ conjSub g '' phi K T z := by
    intro N hN
    have hNw : N ∈ {L | L ∈ centralizingMembers (𝒞 K) {w} ∧ L ≠ M ∧ L ≠ TM} := by
      refine ⟨(hΦw N hN).1, (hΦw N hN).2, fun hEq => ?_⟩
      obtain ⟨L', hL', hL'N, hnc⟩ := exists_noncomm_of_ne S.inClass S.exact S.p1 rf d hKz hT.mem
        hT.ne.symm hKiso hTiso hN.1 hN.2.1 hN.2.2
      have hL'K : L' ≠ K := fun h => hnc (by
        rw [h]
        exact (hKiso N hN.1 hN.2.1).symm)
      have hL'T : L' ≠ T := fun h => hnc (by
        rw [h]
        exact (hTiso N hN.1 hN.2.2).symm)
      have hL'Φ : L' ∈ phi K T z := ⟨hL', hL'K, hL'T⟩
      exact hnc (by
        rw [hEq]
        exact hTM.comm_T L' (hΦw L' hL'Φ).1 (fun h => hL'N (by rw [hEq, h])))
    refine ⟨conjSub g⁻¹ N, ⟨⟨S.inClass.conjInvariant g⁻¹ N hNw.1.1, ?_⟩, ?_, ?_⟩,
      conjSub_conjSub_inv g N⟩
    · have := conjSub_le_centralizer_singleton hNw.1.2 g⁻¹
      rwa [show g⁻¹ * w * g⁻¹⁻¹ = z by rw [hw]; group] at this
    · intro h
      apply hNw.2.1
      rw [hMdef, ← h, conjSub_conjSub_inv]
    · intro h
      apply hNw.2.2
      rw [hTMdef, ← h, conjSub_conjSub_inv]
  exact (Set.eq_of_subset_of_ncard_le hΦsub (Set.ncard_image_le (Set.toFinite _))
    (Set.toFinite _)).symm

theorem conjSub_xGen_eq (S : RouteDSetup p f K z) (hrow : TwinRow tY nY)
    (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z) (hT : IsTwinAt (𝒞 K) K T z) (g : G)
    (hg : ∀ N ∈ phi K T z, Commutes (conjSub g K) N) :
    conjSub g (xGen K T z) = xGen K T z := by
  unfold xGen
  rw [conjSub_iSup₂, conjSub_phi_eq S hrow hshape hT g hg]

end Count

end CFSG.ClassicalInvolution.RouteD.TWS8
