module

public import CFSG.ClassicalInvolution.RouteD.TwinRowsOpen
public import CFSG.ClassicalInvolution.RouteD.TWELarge
public import CFSG.ClassicalInvolution.RouteD.TwinYR2XO
public import CFSG.ClassicalInvolution.RouteD.TWS6SRow
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
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Disconnected
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

local notation "LTag" => CFSG.Assembly.LowTwoRank.StatedLieTag

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.RouteD.TWT6

section Statement

variable (p f : ℕ) [Fact p.Prime]

@[expose] def TwinYNoCentralMod (P : LTag → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (tY : LTag) (nY : ℕ),
      TwinRow tY nY → P tY nY → LocalShapeT p f 2 tY nY (𝒞 K) z → ∀ T : Subgroup G,
      IsTwinAt (𝒞 K) K T z → IsClassicalMember p f T z → ∀ e : TwinElt K T z,
      ∀ M ∈ centralizingMembers (𝒞 K) {e.u},
        ∃ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K ∧ N ≠ T ∧
          ¬ ∀ a ∈ M, ∀ b ∈ N, a * b * a⁻¹ * b⁻¹ ∈ oddCoreIn (centLayer (𝒞 K) e.u)

end Statement

section Reduction

variable {p f : ℕ} [Fact p.Prime] {P : LTag → ℕ → Prop}


theorem twinYNoCentralOn_of_mod (h : TwinYNoCentralMod p f P) : TwinYNoCentralOn p f P := by
  intro G _ _ _ hnab K z S tY nY hrow hP hshape T hT clsT e M hM
  obtain ⟨N, hN, hNK, hNT, hnc⟩ := h G hnab K z S tY nY hrow hP hshape T hT clsT e M hM
  refine ⟨N, hN, hNK, hNT, fun hc => hnc fun a ha b hb => ?_⟩
  have h1 : a * b = b * a := hc a ha b hb
  have h2 : a * b * a⁻¹ * b⁻¹ = 1 := by rw [h1]; group
  rw [h2]
  exact Subgroup.one_mem _

theorem exists_cover_of_mod {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {K T : Subgroup G} {z : G} {tY : LTag} {nY : ℕ}
    (S : RouteDSetup p f K z) (hrow : TwinRow tY nY) (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z)
    (hT : IsTwinAt (𝒞 K) K T z) (clsT : IsClassicalMember p f T z) (e : TwinElt K T z)
    (hMod : ∀ M ∈ centralizingMembers (𝒞 K) {e.u}, ∃ N ∈ centralizingMembers (𝒞 K) {z},
      N ≠ K ∧ N ≠ T ∧
        ¬ ∀ a ∈ M, ∀ b ∈ N, a * b * a⁻¹ * b⁻¹ ∈ oddCoreIn (centLayer (𝒞 K) e.u))
    {J : Subgroup G} (hJ : J ∈ centralizingMembers (𝒞 K) {z}) (hJK : J ≠ K) (hJT : J ≠ T)
    {B : Subgroup G} (huB : e.u ∈ B) :
    ∀ M ∈ centMembers (𝒞 K) e.u, ∃ g : G, e.u ∈ conjSub g B ∧
      InCommonComponent e.u M (conjSub g J) := by
  intro M hM
  obtain ⟨N, hN, hNK, hNT, hnc⟩ := hMod M hM
  have hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  have hNu : N ∈ centralizingMembers (𝒞 K) {e.u} :=
    e.mem_centralizingMembers_u hN.1 (hKiso N hN hNK).symm (hTiso N hN hNT).symm
  have hKT : Commutes K T := hT.comm_K T hT.mem hT.ne
  obtain ⟨-, hunc⟩ := twinElt_u_not_central hnab S e hKT
  have hcc : InCommonComponent e.u M N := by
    by_contra hno
    exact hnc (comm_mod_of_not_inCommonComponent S.odd S.inClass S.ih hunc hM hNu hno)
  obtain ⟨y, hy, hyJ⟩ := twinYXOrbit p f G hnab K z S tY nY hrow hshape T hT clsT e J hJ hJK hJT
    N hN hNK hNT
  refine ⟨y, ?_, by rw [hyJ]; exact hcc⟩
  rw [mem_conjSub_iff]
  have hyu : y * e.u = e.u * y := Subgroup.mem_centralizer_singleton_iff.mp
    (centralizingLayer_le_centralizer (𝒞 K) {e.u} hy)
  have e1 : y⁻¹ * e.u * y = e.u := by
    calc y⁻¹ * e.u * y = y⁻¹ * (e.u * y) := by group
      _ = y⁻¹ * (y * e.u) := by rw [hyu]
      _ = e.u := by group
  rw [e1]
  exact huB

theorem twinYP1On_of_mod (hΩall : HypOmegaModAll p f) (hAT : TWE.AEmptyTwinRowOn p f P)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) (hGenT : TwinYGenTOn p f P)
    (hMod : TwinYNoCentralMod p f P) : TwinYP1On p f P := by
  intro G _ _ _ hnab K z S tY nY hrow hP hshape T hT clsT e
  have hcen : Subgroup.center G = ⊥ := CoreAssembly.center_eq_bot hnab
  have hΩ : HypOmegaMod p f (𝒞 K) := hΩall G hnab S.odd S.five K z S.cls S.below
  have hA : ∀ M ∈ 𝒞 K, AEmpty (𝒞 K) M := hAT G hnab K z S tY nY hrow hP hshape
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
  obtain ⟨hu1, hunc⟩ := twinElt_u_not_central hnab S e hKT
  have fd : TwinFrameData (𝒞 K) K T z e.u J t :=
    twinFrameData_of S hΩ e hT.mem.1 hT.ne hKT clsT hJ.1 hJ.2 hJt htz hJKc hJTc
  have hbal := rankThreeBalance_of hH S hΩ hA h7 fd
  have hframe := frameSide_of S hcen hΩ hD4 rf hshape e fd hT.mem hT.ne.symm hKiso hTiso clsT hJ
    hJK hJT hJt (hGenT G hnab K z S tY nY hrow hP hshape T hT clsT e J t hJ hJK hJT hJt)
  have hgen := rankTwoSpan_eq_top_of S hframe
  have huB : e.u ∈ Subgroup.closure ({z, e.u, t} : Set G) := Subgroup.subset_closure (by simp)
  have htB : t ∈ Subgroup.closure ({z, e.u, t} : Set G) := Subgroup.subset_closure (by simp)
  have hcov := exists_cover_of_mod hnab S hrow hshape hT clsT e
    (hMod G hnab K z S tY nY hrow hP hshape T hT clsT e) hJ hJK hJT huB
  exact (stage2_of_balanced_gen hnab S.odd S.five S.inClass S.ih hbal hJ.1 hJt htB
    (le_centralizer_frame e hJ.2 hJt hJKc hJTc) hgen).2 e.u hu1 hcov

theorem twinYVisibleOn_of_mod (hΩall : HypOmegaModAll p f) (hAT : TWE.AEmptyTwinRowOn p f P)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) (hGenT : TwinYGenTOn p f P)
    (hMod : TwinYNoCentralMod p f P) : TwinYVisibleOn p f P := by
  have hP1 := twinYP1On_of_mod hΩall hAT hP4 hH hGenT hMod
  have hR2 := TWE.twinYTransitiveOn_of_p1_rowT hΩall hAT hP1 (twinYNoCentralOn_of_mod hMod)
  intro G _ _ _ hnab K z S tY nY hrow hP hshape T hT clsT e J t hJ hJK hJT hJt M hM hMt hMJ
  have hP1u : LocalOddCentral (𝒞 K) {e.u} := hP1 G hnab K z S tY nY hrow hP hshape T hT clsT e
  have hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  have hJu : J ∈ centralizingMembers (𝒞 K) {e.u} :=
    e.mem_centralizingMembers_u hJ.1 (hKiso J hJ hJK).symm (hTiso J hJ hJT).symm
  obtain ⟨g, hg⟩ := hR2 G hnab K z S tY nY hrow hP hshape T hT clsT e (locImg (𝒞 K) e.u J)
    (mem_locFamily_iff.mpr ⟨J, hJu, rfl⟩) (locImg (𝒞 K) e.u M)
    (mem_locFamily_iff.mpr ⟨M, hM, rfl⟩)
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
  have hyloc : locImg (𝒞 K) e.u (conjSub (y : G) J) = locImg (𝒞 K) e.u M := by
    rw [locImg_conjSub_layer J y]
    exact hg
  have hyz : (y : G) ∈ Subgroup.centralizer ({e.u} : Set G) :=
    centralizingLayer_le_centralizer (𝒞 K) {e.u} y.2
  have hJy : conjSub (y : G) J ∈ centralizingMembers (𝒞 K) {e.u} := by
    refine ⟨S.inClass.conjInvariant _ J hJu.1, fun x hx => ?_⟩
    have h1 : (y : G)⁻¹ * x * y ∈ J := mem_conjSub_iff.mp hx
    have h2 := hJu.2 h1
    have e2 : x = (y : G) * ((y : G)⁻¹ * x * y) * (y : G)⁻¹ := by group
    rw [e2]
    exact mul_mem (mul_mem hyz h2) (inv_mem hyz)
  exact ⟨y, hyz, locImg_injOn S.inClass hP1u hJy hM hyloc⟩

theorem twinYVisibleOn_odd3_of_mod (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩall : HypOmegaModAll p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) (hcls : TwinInvolution p f)
    (hMod : TwinYNoCentralMod p f fun t n => t = .POmegaOdd ∧ n = 3) :
    TwinYVisibleOn p f fun t n => t = .POmegaOdd ∧ n = 3 :=
  twinYVisibleOn_of_mod hΩall
    (TWE.AEmptyTwinRow.on (TWE.Big.aEmptyTwinRow_proved hΩall hcls)) hP4 hH
    (twinYGenTOn_of_model fun tY nY _ hl => by
      obtain ⟨rfl, rfl⟩ := hl
      exact twinMFGeneration_odd hp2 hq (le_refl 3))
    hMod

theorem twinYVisibleOn_minus4_of_mod (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩall : HypOmegaModAll p f) (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f)
    (hcls : TwinInvolution p f)
    (hMod : TwinYNoCentralMod p f fun t n => t = .POmegaMinus ∧ n = 4) :
    TwinYVisibleOn p f fun t n => t = .POmegaMinus ∧ n = 4 :=
  twinYVisibleOn_of_mod hΩall
    (TWE.AEmptyTwinRow.on (TWE.Big.aEmptyTwinRow_proved hΩall hcls)) hP4 hH
    (twinYGenTOn_of_model fun tY nY _ hl => by
      obtain ⟨rfl, rfl⟩ := hl
      exact twinMFGeneration_minus hp2 hq (le_refl 4))
    hMod

theorem twinVisNCOpen_of_noCentralMod (hΩall : HypOmegaModAll p f) (hP4 : Ih8G2D4 p f)
    (hH : TwinFrameHyp51 p f) (hcls : TwinInvolution p f)
    (hB3 : TwinYNoCentralMod p f fun t n => t = .POmegaOdd ∧ n = 3)
    (hTD4 : TwinYNoCentralMod p f fun t n => t = .POmegaMinus ∧ n = 4) :
    TwinVisNCOpen p f where
  visB3 := by
    intro G _ _ _ hnab K z S
    exact twinYVisibleOn_odd3_of_mod S.odd S.five hΩall hP4 hH hcls hB3 G hnab K z S
  ncB3 := twinYNoCentralOn_of_mod hB3
  visTD4 := by
    intro G _ _ _ hnab K z S
    exact twinYVisibleOn_minus4_of_mod S.odd S.five hΩall hP4 hH hcls hTD4 G hnab K z S
  ncTD4 := twinYNoCentralOn_of_mod hTD4

end Reduction

end CFSG.ClassicalInvolution.RouteD.TWT6
