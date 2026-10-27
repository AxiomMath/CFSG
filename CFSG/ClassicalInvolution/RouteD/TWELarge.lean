module

public import CFSG.ClassicalInvolution.RouteD.TWSReduce
public import CFSG.ClassicalInvolution.RouteD.TWYRankLarge
public import CFSG.ClassicalInvolution.RouteD.TWDConfig
public import CFSG.ClassicalInvolution.RouteD.TWEAssemble
public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootRows
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

namespace CFSG.ClassicalInvolution.RouteD.TWE

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.WeakCT
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

local notation "LTag" => CFSG.Assembly.LowTwoRank.StatedLieTag

set_option linter.unusedSectionVars false

section AEmpty

variable (p f : ℕ) [Fact p.Prime]

@[expose] def AEmptyTwinRowOn (P : LTag → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (tY : LTag) (nY : ℕ),
      TwinRow tY nY → P tY nY → LocalShapeT p f 2 tY nY (𝒞 K) z → ∀ M ∈ 𝒞 K, AEmpty (𝒞 K) M

end AEmpty

theorem AEmptyTwinRow.on {p f : ℕ} [Fact p.Prime] {P : LTag → ℕ → Prop} (h : AEmptyTwinRow p f) :
    AEmptyTwinRowOn p f P :=
  fun G _ _ _ hnab K z S tY nY hrow _ hshape => h G hnab K z S tY nY hrow hshape



section Rows

variable {p f : ℕ} [Fact p.Prime] {P : LTag → ℕ → Prop}

theorem twinYP1On_of_visible_rowT (hΩall : HypOmegaModAll p f) (hAT : AEmptyTwinRowOn p f P)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) (hGenT : TwinYGenTOn p f P)
    (hVis : TwinYVisibleOn p f P) : TwinYP1On p f P := by
  intro G _ _ _ hnab K z S tY nY hrow hP hshape T hT clsT e
  have hcen : Subgroup.center G = ⊥ := CoreAssembly.center_eq_bot hnab
  have hΩ : HypOmegaMod p f (𝒞 K) := hΩall G hnab S.odd S.five K z S.cls S.below
  have hA : ∀ M ∈ 𝒞 K, AEmpty (𝒞 K) M :=
    hAT G hnab K z S tY nY hrow hP hshape
  have h7 : Thm7TypedBelow p f (Nat.card G) := thm7TypedBelow_of hP4 S.below
  obtain ⟨hG2, hD4, hnA1⟩ := hrow.tag_facts
  have rf := LocalShapeT.twinRowFacts hshape S.odd S.five hG2 hD4 hnA1
  have hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  obtain ⟨J, J', t, hJ, hJK, hJT, hJt, htz, hJ't, hJJ', hJ'u⟩ :=
    exists_frameMembers hnab S hrow hshape hT clsT e
  have hKT : Commutes K T := hT.comm_K T hT.mem hT.ne
  have hJKc : Commutes J K := (hKiso J hJ hJK).symm
  have hJTc : Commutes J T := (hTiso J hJ hJT).symm
  have hJu : J ∈ centralizingMembers (𝒞 K) {e.u} := e.mem_centralizingMembers_u hJ.1 hJKc hJTc
  obtain ⟨hu1, hunc⟩ := twinElt_u_not_central hnab S e hKT
  have fd : TwinFrameData (𝒞 K) K T z e.u J t :=
    twinFrameData_of S hΩ e hT.mem.1 hT.ne hKT clsT hJ.1 hJ.2 hJt htz hJKc hJTc
  have hbal := rankThreeBalance_of hH S hΩ hA h7 fd
  have hframe := frameSide_of S hcen hΩ hD4 rf hshape e fd hT.mem hT.ne.symm hKiso hTiso clsT hJ
    hJK hJT hJt (hGenT G hnab K z S tY nY hrow hP hshape T hT clsT e J t hJ hJK hJT hJt)
  have hgen := rankTwoSpan_eq_top_of S hframe
  have huB : e.u ∈ Subgroup.closure ({z, e.u, t} : Set G) := Subgroup.subset_closure (by simp)
  have htB : t ∈ Subgroup.closure ({z, e.u, t} : Set G) := Subgroup.subset_closure (by simp)
  have hcov := cover_of_visible S.odd S.five hΩ S.inClass S.exact S.ih hunc huB hJu
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five hJt)
    (hVis G hnab K z S tY nY hrow hP hshape T hT clsT e J t hJ hJK hJT hJt)
  exact (stage2_of_balanced_gen hnab S.odd S.five S.inClass S.ih hbal hJ.1 hJt htB
    (le_centralizer_frame e hJ.2 hJt hJKc hJTc) hgen).2 e.u hu1 hcov

theorem twinYTransitiveOn_of_p1_rowT (hΩall : HypOmegaModAll p f) (hAT : AEmptyTwinRowOn p f P)
    (hP1 : TwinYP1On p f P) (hNC : TwinYNoCentralOn p f P) : TwinYTransitiveOn p f P := by
  intro G _ _ _ hnab K z S tY nY hrow hP hshape T hT clsT e K₁ hK₁ L hL
  have hΩ : HypOmegaMod p f (𝒞 K) := hΩall G hnab S.odd S.five K z S.cls S.below
  have hA : ∀ M ∈ 𝒞 K, AEmpty (𝒞 K) M :=
    hAT G hnab K z S tY nY hrow hP hshape
  have hP1u : LocalOddCentral (𝒞 K) {e.u} := hP1 G hnab K z S tY nY hrow hP hshape T hT clsT e
  have hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  obtain ⟨J, J', t, hJ, hJK, hJT, -, -, -, -, -⟩ :=
    exists_frameMembers hnab S hrow hshape hT clsT e
  have hKT : Commutes K T := hT.comm_K T hT.mem hT.ne
  have hMemU : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → N ≠ T →
      N ∈ centralizingMembers (𝒞 K) {e.u} := fun N hN hNK hNT =>
    e.mem_centralizingMembers_u hN.1 (hKiso N hN hNK).symm (hTiso N hN hNT).symm
  have hJu := hMemU J hJ hJK hJT
  obtain ⟨-, hunc⟩ := twinElt_u_not_central hnab S e hKT
  have hJΦ : locImg (𝒞 K) e.u J ∈ locFamily (𝒞 K) e.u := mem_locFamily_iff.mpr ⟨J, hJu, rfl⟩
  have key : ∀ M ∈ locFamily (𝒞 K) e.u,
      ∃ g : locQuot (𝒞 K) e.u, conjSub g (locImg (𝒞 K) e.u J) = M := by
    intro M hM
    by_contra hno
    push Not at hno
    obtain ⟨M₀, hM₀, rfl⟩ := mem_locFamily_iff.mp hM
    have hle := normalClosure_le_centralizer_of_not_conj S.odd S.five hΩ hA S.below hunc hJΦ hM hno
    obtain ⟨N, hN, hNK, hNT, hNc⟩ := hNC G hnab K z S tY nY hrow hP hshape T hT clsT e M₀ hM₀
    obtain ⟨y, hy, hyN⟩ :=
      twinYXOrbit p f G hnab K z S tY nY hrow hshape T hT clsT e J hJ hJK hJT N hN hNK hNT
    have hNu := hMemU N hN hNK hNT
    apply hNc
    refine commutes_of_commutes_locImg S.inClass hP1u hM₀ hNu ?_
    intro a ha b hb
    rw [← hyN, locImg_conjSub_layer J ⟨y, hy⟩] at hb
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hb
    have hbN : (MulAut.conj (locMk (𝒞 K) e.u ⟨y, hy⟩)).toMonoidHom j ∈
        Subgroup.normalClosure (locImg (𝒞 K) e.u J : Set (locQuot (𝒞 K) e.u)) :=
      (Subgroup.normalClosure_normal).conj_mem j (Subgroup.subset_normalClosure hj) _
    exact Subgroup.mem_centralizer_iff.mp (hle hbN) a ha
  obtain ⟨g₁, hg₁⟩ := key K₁ hK₁
  obtain ⟨g₂, hg₂⟩ := key L hL
  refine ⟨g₂ * g₁⁻¹, ?_⟩
  rw [← hg₁, ← conjSub_mul, inv_mul_cancel_right]
  exact hg₂

theorem exists_orthLie_twinOn_rowT (hΩall : HypOmegaModAll p f) (hAT : AEmptyTwinRowOn p f P)
    (hP4 : Ih8G2D4 p f) (hTrans : TwinYTransitiveOn p f P) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) {K T : Subgroup G} {z : G}
    (S : RouteDSetup p f K z) {tY : LTag} {nY : ℕ} (hrow : TwinRow tY nY)
    (hP : P tY nY) (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z) (hT : IsTwinAt (𝒞 K) K T z)
    (clsT : IsClassicalMember p f T z) (e : TwinElt K T z) :
    ∃ D : LieSystemData p f (locQuot (𝒞 K) e.u) (locFamily (𝒞 K) e.u), D.card = 1 ∧
      ∃ i : Fin D.card, ∃ (d : ℕ) (ε : Bool), 5 ≤ d ∧ IsOrthTag d ε (D.tag i) (D.rank i) := by
  have hΩ : HypOmegaMod p f (𝒞 K) := hΩall G hnab S.odd S.five K z S.cls S.below
  have hA : ∀ M ∈ 𝒞 K, AEmpty (𝒞 K) M :=
    hAT G hnab K z S tY nY hrow hP hshape
  obtain ⟨J, J', t, hJ, hJK, hJT, hJt, htz, hJ't, hJJ', hJ'u⟩ :=
    exists_frameMembers hnab S hrow hshape hT clsT e
  have hKT : Commutes K T := hT.comm_K T hT.mem hT.ne
  have hJKc : Commutes J K := (hT.comm_K J hJ hJK).symm
  have hJTc : Commutes J T := (hT.comm_T J hJ hJT).symm
  have hJu : J ∈ centralizingMembers (𝒞 K) {e.u} := e.mem_centralizingMembers_u hJ.1 hJKc hJTc
  obtain ⟨-, hunc⟩ := twinElt_u_not_central hnab S e hKT
  have htw := twin_locFamily S.inClass S.exact hJu hJ'u
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five hJt)
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five hJ't) hJJ'
  exact exists_orthLie_of_trans S.odd S.five hΩ hA hP4 S.below hunc
    (hTrans G hnab K z S tY nY hrow hP hshape T hT clsT e) htw

theorem twinYTypeOn_of_inputs_rowT (hΩall : HypOmegaModAll p f) (hAT : AEmptyTwinRowOn p f P)
    (hP4 : Ih8G2D4 p f) (hTrans : TwinYTransitiveOn p f P) (hRank : TwinYRankOn p f P) :
    TwinYTypeOn p f P := by
  intro G _ _ _ hnab K z S tY nY hrow hP hshape T hT clsT e _
  obtain ⟨D, hcard, i, horth⟩ :=
    exists_orthLie_twinOn_rowT hΩall hAT hP4 hTrans hnab S hrow hP hshape hT clsT e
  obtain ⟨hd, hr⟩ := hRank G hnab K z S tY nY hrow hP hshape T hT clsT e D hcard i horth
  have h := NonClassical.localShapeT_zero_of_card_eq_one D hcard i
  rwa [hd, hr] at h


theorem twinYP1On_large_of_aEmptyTwinRow (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩall : HypOmegaModAll p f) (hAT : AEmptyTwinRowOn p f TwinRow.large)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) : TwinYP1On p f TwinRow.large :=
  twinYP1On_of_visible_rowT hΩall hAT hP4 hH
    (twinYGenTOn_of_model fun tY nY _ hl => twinMFGeneration_large hp2 hq tY nY hl)
    (twinYVisibleOn_of_model fun tY nY _ hl => twinMFCentralizing_large hp2 hq tY nY hl)

theorem twinYTypeOn_large_of_aEmptyTwinRow (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩall : HypOmegaModAll p f) (hAT : AEmptyTwinRowOn p f TwinRow.large)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) : TwinYTypeOn p f TwinRow.large :=
  twinYTypeOn_of_inputs_rowT hΩall hAT hP4
    (twinYTransitiveOn_of_p1_rowT hΩall hAT
      (twinYP1On_large_of_aEmptyTwinRow hp2 hq hΩall hAT hP4 hH)
      (twinYNoCentralOn_of_model fun tY nY _ hl => twinMFCommutant_large hp2 hq tY nY hl))
    (TWY.twinYRankOn_large hp2 hq (twinYP1On_large_of_aEmptyTwinRow hp2 hq hΩall hAT hP4 hH))

end Rows

end CFSG.ClassicalInvolution.RouteD.TWE
