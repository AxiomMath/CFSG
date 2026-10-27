module

public import CFSG.ClassicalInvolution.RouteD.TWT6Mod
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
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Balance.BootRank3
  CFSG.ClassicalInvolution.Disconnected
open CFSG.Open (classicalInvolutionOddCore componentClassificationOddCore)

local notation "𝒞" => CoreAssembly.conjClass

local notation "LTag" => CFSG.Assembly.LowTwoRank.StatedLieTag

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.RouteD.TWT6

section Generic

theorem hom_eq_one_of_perfect_of_solvable {G H : Type*} [Group G] [Group H] [Group.IsPerfect G]
    [Group.IsSolvable H] (φ : G →* H) : φ = 1 := by
  have : Group.IsPerfect ↥φ.range := Group.IsPerfect.ofSurjective φ.rangeRestrict_surjective
  have hr : φ.range = ⊥ := by
    by_contra hne
    have : Nontrivial ↥φ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥φ.range
    exact (ne_of_lt h1) (Group.IsPerfect.commutator_eq_top (G := ↥φ.range))
  exact MonoidHom.range_eq_bot_iff.mp hr

theorem commutes_of_commutator_mem_oddCore {G : Type} [Group G] [Finite G] {O : Subgroup G}
    (hOodd : Odd (Nat.card O)) {M N : Subgroup G} (hNperf : Group.IsPerfect ↥N)
    (hNO : ∀ d ∈ O, ∀ k ∈ N, d * k = k * d)
    (hMN : ∀ a ∈ M, ∀ b ∈ N, a * b * a⁻¹ * b⁻¹ ∈ O) :
    ∀ a ∈ M, ∀ b ∈ N, a * b = b * a := by
  intro a ha
  have hsolv : Group.IsSolvable ↥O := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hOodd
  let φ : ↥N →* ↥O :=
    { toFun := fun b => ⟨a * b * a⁻¹ * (b : G)⁻¹, hMN a ha b b.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun b b' => by
        apply Subtype.ext
        have hc : (b : G) * (a * b' * a⁻¹ * (b' : G)⁻¹) =
            (a * b' * a⁻¹ * (b' : G)⁻¹) * b := (hNO _ (hMN a ha b' b'.2) b b.2).symm
        calc a * ((b : G) * b') * a⁻¹ * ((b : G) * b')⁻¹
            = (a * b * a⁻¹ * (b : G)⁻¹) * ((b : G) * (a * b' * a⁻¹ * (b' : G)⁻¹) * (b : G)⁻¹) := by
              group
          _ = (a * b * a⁻¹ * (b : G)⁻¹) * (a * b' * a⁻¹ * (b' : G)⁻¹) := by
              rw [hc]
              group }
  have h0 : φ = 1 := hom_eq_one_of_perfect_of_solvable φ
  intro b hb
  have h1 : φ ⟨b, hb⟩ = 1 := by rw [h0]; rfl
  have h2 : a * b * a⁻¹ * b⁻¹ = 1 := congrArg Subtype.val h1
  calc a * b = (a * b * a⁻¹ * b⁻¹) * b * a := by group
    _ = b * a := by rw [h2]; group

end Generic

section Reduction

variable {p f : ℕ} [Fact p.Prime] {P : LTag → ℕ → Prop}


theorem members_centralize_oddCore (hΩall : HypOmegaModAll p f)
    (hAT : TWE.AEmptyTwinRowOn p f P) (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f)
    (hGenT : TwinYGenTOn p f P) {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G} {z : G} (S : RouteDSetup p f K z)
    {tY : LTag} {nY : ℕ} (hrow : TwinRow tY nY) (hP : P tY nY)
    (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z) {T : Subgroup G}
    (hT : IsTwinAt (𝒞 K) K T z) (clsT : IsClassicalMember p f T z) (e : TwinElt K T z)
    {N : Subgroup G} (hN : N ∈ centralizingMembers (𝒞 K) {z}) (hNK : N ≠ K) (hNT : N ≠ T) :
    ∀ d ∈ oddCoreIn (centLayer (𝒞 K) e.u), ∀ k ∈ N, d * k = k * d := by
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
  have hΔ := (stage2_of_balanced_gen hnab S.odd S.five S.inClass S.ih hbal hJ.1 hJt htB
    (le_centralizer_frame e hJ.2 hJt hJKc hJTc) hgen).1
  obtain ⟨y, hy, hyJ⟩ := twinYXOrbit p f G hnab K z S tY nY hrow hshape T hT clsT e J hJ hJK hJT
    N hN hNK hNT
  have hNu : N ∈ centMembers (𝒞 K) e.u :=
    e.mem_centralizingMembers_u hN.1 (hKiso N hN hNK).symm (hTiso N hN hNT).symm
  have hyu : y * e.u = e.u * y := Subgroup.mem_centralizer_singleton_iff.mp
    (centralizingLayer_le_centralizer (𝒞 K) {e.u} hy)
  have hxy : e.u ∈ conjSub y (Subgroup.closure ({z, e.u, t} : Set G)) := by
    rw [mem_conjSub_iff]
    have e1 : y⁻¹ * e.u * y = e.u := by
      calc y⁻¹ * e.u * y = y⁻¹ * (e.u * y) := by group
        _ = y⁻¹ * (y * e.u) := by rw [hyu]
        _ = e.u := by group
    rw [e1]
    exact huB
  have hcc : InCommonComponent e.u N (conjSub y J) := by
    rw [hyJ]
    exact inCommonComponent_self hnab S.odd S.inClass S.ih hu1 hNu
  intro d hd k hk
  obtain ⟨d', hd', rfl⟩ := hd
  exact member_commutes_oddCore_of_deltaCore_eq_bot hnab S.odd S.five
    CFSG.ClassicalInvolution.ModelFacts.modelClauseZero fundamentalWholeA1 S.inClass S.ih
    (isElemAbelian_two_conjSub hbal.elem y)
    (by
      rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj y).injective]
      exact hbal.card)
    (deltaCore_eq_bot_conjSub hΔ y) hxy hu1 hNu (S.inClass.conjInvariant y J hJ.1) (hJt.conj y)
    (conj_mem_conjSub htB) (conjSub_le_centralizer (le_centralizer_frame e hJ.2 hJt hJKc hJTc) y)
    hcc d' hd' k hk

theorem twinYNoCentralMod_of_noCentral (hΩall : HypOmegaModAll p f)
    (hAT : TWE.AEmptyTwinRowOn p f P) (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f)
    (hGenT : p ≠ 2 → 5 ≤ p ^ f → TwinYGenTOn p f P) (hNC : TwinYNoCentralOn p f P) :
    TwinYNoCentralMod p f P := by
  intro G _ _ _ hnab K z S tY nY hrow hP hshape T hT clsT e M hM
  obtain ⟨N, hN, hNK, hNT, hnc⟩ := hNC G hnab K z S tY nY hrow hP hshape T hT clsT e M hM
  refine ⟨N, hN, hNK, hNT, fun hcomm => hnc ?_⟩
  have hNO := members_centralize_oddCore hΩall hAT hP4 hH (hGenT S.odd S.five) hnab S hrow hP
    hshape hT clsT e hN hNK hNT
  obtain ⟨w, hw⟩ := S.inClass.classical N hN.1
  exact commutes_of_commutator_mem_oddCore (odd_card_oddCoreIn _) hw.perfect hNO hcomm

theorem twinVisNCOpen_of_noCentral (hΩall : HypOmegaModAll p f) (hP4 : Ih8G2D4 p f)
    (hH : TwinFrameHyp51 p f) (hcls : TwinInvolution p f)
    (hB3 : TwinYNoCentralOn p f fun t n => t = .POmegaOdd ∧ n = 3)
    (hTD4 : TwinYNoCentralOn p f fun t n => t = .POmegaMinus ∧ n = 4) :
    TwinVisNCOpen p f :=
  twinVisNCOpen_of_noCentralMod hΩall hP4 hH hcls
    (twinYNoCentralMod_of_noCentral hΩall
      (TWE.AEmptyTwinRow.on (TWE.Big.aEmptyTwinRow_proved hΩall hcls)) hP4 hH
      (fun hp2 hq => twinYGenTOn_of_model fun tY nY _ hl => by
        obtain ⟨rfl, rfl⟩ := hl
        exact twinMFGeneration_odd hp2 hq (le_refl 3)) hB3)
    (twinYNoCentralMod_of_noCentral hΩall
      (TWE.AEmptyTwinRow.on (TWE.Big.aEmptyTwinRow_proved hΩall hcls)) hP4 hH
      (fun hp2 hq => twinYGenTOn_of_model fun tY nY _ hl => by
        obtain ⟨rfl, rfl⟩ := hl
        exact twinMFGeneration_minus hp2 hq (le_refl 4)) hTD4)

end Reduction

end CFSG.ClassicalInvolution.RouteD.TWT6
