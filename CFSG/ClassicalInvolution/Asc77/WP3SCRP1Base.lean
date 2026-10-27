module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootRows
public import CFSG.ClassicalInvolution.Asc77.WP3SCRBoot
public import CFSG.ClassicalInvolution.RouteD.TwinYR2Model
public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinModels
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.WP3FrameModelPSU
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
import CFSG.ClassicalInvolution.Balance.PassTwoModelFacts
import CFSG.ClassicalInvolution.Balance.BootNoTriple
import CFSG.ClassicalInvolution.SmallCases.DSplitDefs
public import CFSG.ClassicalInvolution.Balance.BootNoTripleStrong
public import CFSG.ClassicalInvolution.RouteD.G2D4Ih8
import CFSG.ClassicalInvolution.Asc77.AscE187Cop
import CFSG.ClassicalInvolution.Asc77.AscThmABasic

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD.TwinY

local notation "𝒞" => CoreAssembly.conjClass

local notation "LTag" => CFSG.Assembly.LowTwoRank.StatedLieTag

section Shape

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem twinLieShape_of_local (hex : ExactMembers Ω)
    (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z)
    (hs : ∃ D : LocalLieSystemAt p f Ω z, TwinShapeData D) : TwinLieShape p f Ω z := by
  have h : centralizingMembers (exactFamily Ω z) {z} = centralizingMembers Ω {z} :=
    (centMembers_exactFamily Ω z).trans (exactFamily_eq_centMembers_of_exact hex hcls)
  have key : ∀ S₁ S₂ : Set (Subgroup G), S₁ = S₂ →
      (∃ D : LieSystemData p f (↥(⨆ L ∈ S₁, L) ⧸ classicalInvolutionOddCore ↥(⨆ L ∈ S₁, L))
        (oddQuotientFamily (restrictFamily S₁ (⨆ L ∈ S₁, L))), TwinShapeData D) →
      ∃ D : LieSystemData p f (↥(⨆ L ∈ S₂, L) ⧸ classicalInvolutionOddCore ↥(⨆ L ∈ S₂, L))
        (oddQuotientFamily (restrictFamily S₂ (⨆ L ∈ S₂, L))), TwinShapeData D := by
    intro S₁ S₂ h
    subst h
    exact id
  exact key _ _ h.symm hs

omit [Finite G] in
theorem exists_twinShapeData_of_localShapeT {tY : LTag} {nY : ℕ} (hL : ListedTwin tY nY)
    (h : LocalShapeT p f 2 tY nY Ω z) : ∃ D : LocalLieSystemAt p f Ω z, TwinShapeData D := by
  obtain ⟨D, hcard, i₁, htag, hrank, hrest⟩ := h
  have hlt := i₁.isLt
  obtain ⟨i₀, i₂, h01, h12, h02⟩ : ∃ i₀ i₂ : Fin D.card, i₀ ≠ i₁ ∧ i₁ ≠ i₂ ∧ i₀ ≠ i₂ := by
    refine ⟨⟨if i₁.val = 0 then 1 else 0, by split_ifs <;> omega⟩,
      ⟨if i₁.val = 2 then 1 else 2, by split_ifs <;> omega⟩, ?_, ?_, ?_⟩ <;>
    · intro hh
      have := congrArg Fin.val hh
      simp only at this
      split_ifs at this <;> omega
  refine ⟨D, hcard, i₀, i₁, i₂, h01, h12, h02, (hrest i₀ h01).1, (hrest i₀ h01).2,
    (hrest i₂ h12.symm).1, (hrest i₂ h12.symm).2, ?_⟩
  rw [htag, hrank]
  exact hL

end Shape

section AEmpty

variable {p f : ℕ} [Fact p.Prime]

theorem aEmpty_of_twinExact (hAE : AEmptyTwinExact p f) (hcls : TwinInvolution p f)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    {K : Subgroup G} {z : G} (S : RouteDSetup p f K z) {tY : LTag} {nY : ℕ}
    (hrow : TwinRow tY nY) (hL : ListedTwin tY nY) (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z) :
    ∀ M ∈ 𝒞 K, AEmpty (𝒞 K) M := by
  have hcen : Subgroup.center G = ⊥ := CoreAssembly.center_eq_bot hnab
  obtain ⟨hG2, hD4, hnA1⟩ := hrow.tag_facts
  have hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N := fun N hN hNK =>
    (S.cp_at_member hcen (CoreAssembly.mem_conjClass_self K) S.cls hN).resolve_right hNK
  obtain ⟨T, hT, hTK, hTiso⟩ : ∃ T ∈ centralizingMembers (𝒞 K) {z}, T ≠ K ∧
      ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N := by
    obtain ⟨D, hcard, i₁, htag, hrank, hrest⟩ := hshape
    have hbig : ¬ (D.tag i₁ = .PSL ∧ D.rank i₁ = 2) := fun ⟨h1, h2⟩ =>
      hnA1 ⟨htag.symm.trans h1, hrank.symm.trans h2⟩
    exact exists_twin_of_layer (Gaps.fundNoncentral p) S.inClass S.exact S.p1 D i₁
      (by omega) hrest hbig (CoreAssembly.mem_conjClass_self K) S.cls
  have hTwin : IsTwinAt (𝒞 K) K T z := ⟨hT, hTK, hTiso, hKiso⟩
  have clsT : IsClassicalMember p f T z := hcls G hnab K z S tY nY hrow hshape T hTwin
  have hTE : TwinExactShape p f K z :=
    ⟨twinLieShape_of_local S.exact S.inClass.classical
      (exists_twinShapeData_of_localShapeT hL hshape), T, hT.1, hKiso T hT hTK, clsT⟩
  exact hAE G hnab S.odd S.five K z S.cls S.below hTE

end AEmpty

section Rows

variable {p f : ℕ} [Fact p.Prime]

theorem p1_of_twin_at_row {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G} {z : G} (S : RouteDSetup p f K z)
    (hΩ : HypOmegaMod p f (𝒞 K)) (hA : ∀ N ∈ 𝒞 K, AEmpty (𝒞 K) N)
    (h7 : Thm7TypedBelow p f (Nat.card G)) (hH : TwinFrameHyp51 p f) {tY : LTag} {nY : ℕ}
    (hGenR : TwinYGenTOn p f (fun t n => t = tY ∧ n = nY))
    (hcls : TwinInvolution p f) (hrow : TwinRow tY nY)
    (hno3 : NoThreeFund p f tY nY) (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z)
    {M : Subgroup G} (hM : M ∈ 𝒞 K) {w : G}
    (hw : IsClassicalMember p f M w) (hKM : Commutes K M) (hzw : z ≠ w) :
    LocalOddCentral (𝒞 K) {z * w} := by
  have hcen : Subgroup.center G = ⊥ := CoreAssembly.center_eq_bot hnab
  obtain ⟨hG2, hD4, hnA1⟩ := hrow.tag_facts
  have rf := LocalShapeT.twinRowFacts hshape S.odd S.five hG2 hD4 hnA1
  obtain ⟨d⟩ := LocalShapeT.nonempty_dictT2 hD4 rf.fsc S.inClass
    (CoreAssembly.mem_conjClass_self K) S.cls hshape
  have hKmem : K ∈ centralizingMembers (𝒞 K) {z} :=
    ⟨CoreAssembly.mem_conjClass_self K, le_centralizer_of_isClassicalMember S.cls⟩
  have hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N := fun N hN hNK =>
    (S.cp_at_member hcen (CoreAssembly.mem_conjClass_self K) S.cls hN).resolve_right hNK
  obtain ⟨T, hT, hTK, hTiso⟩ : ∃ T ∈ centralizingMembers (𝒞 K) {z}, T ≠ K ∧
      ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N := by
    obtain ⟨D, hcard, i₁, htag, hrank, hrest⟩ := hshape
    have hbig : ¬ (D.tag i₁ = .PSL ∧ D.rank i₁ = 2) := fun ⟨h1, h2⟩ =>
      hnA1 ⟨htag.symm.trans h1, hrank.symm.trans h2⟩
    exact exists_twin_of_layer (Gaps.fundNoncentral p) S.inClass S.exact S.p1 D i₁
      (by omega) hrest hbig (CoreAssembly.mem_conjClass_self K) S.cls
  have hTwin : IsTwinAt (𝒞 K) K T z := ⟨hT, hTK, hTiso, hKiso⟩
  have clsT : IsClassicalMember p f T z := hcls G hnab K z S tY nY hrow hshape T hTwin
  have hKT : Commutes K T := hKiso T hT hTK
  have hUz := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five S.cls
  have hUT := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five clsT
  have hUw := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five hw
  have hMz : M ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hKM z S.cls.mem x hx).symm
  have hJ : M ∈ centralizingMembers (𝒞 K) {z} := ⟨hM, hMz⟩
  have hJK : M ≠ K := by
    intro h
    rw [h] at hUw
    exact hzw (hUz.eq hUw)
  have hJT : M ≠ T := by
    intro h
    rw [h] at hUw
    exact hzw (hUT.eq hUw)
  have hJKc : Commutes M K := hKM.symm
  have hJTc : Commutes M T := (hTiso M hJ hJT).symm
  have cfg : TwinCfg p f K T M z w :=
    ⟨hT, fun h => hTK h.symm, hKiso, hTiso, clsT, hJ, hJK, hJT, hw, hzw.symm⟩
  obtain ⟨e⟩ := exists_twinElt S.cls clsT (S.exact K (CoreAssembly.mem_conjClass_self K))
    (S.exact T hT.1) (odd_natCard_galoisField S.odd S.five)
  have fd : TwinFrameData (𝒞 K) K T z e.u M w :=
    twinFrameData_of S hΩ e hT.1 hTK hKT clsT hM hMz hw hzw.symm hJKc hJTc
  have hbal := rankThreeBalance_of hH S hΩ hA h7 fd
  have hframe := frameSide_of S hcen hΩ hD4 rf hshape e fd hT (fun h => hTK h.symm) hKiso hTiso
    clsT hJ hJK hJT hw
    (hGenR G hnab K z S tY nY hrow ⟨rfl, rfl⟩ hshape T hTwin clsT e M w hJ hJK hJT hw)
  have hgen := rankTwoSpan_eq_top_of S hframe
  have hzB : z ∈ Subgroup.closure ({z, e.u, w} : Set G) := Subgroup.subset_closure (by simp)
  have hwB : w ∈ Subgroup.closure ({z, e.u, w} : Set G) := Subgroup.subset_closure (by simp)
  have hx1 : z * w ≠ 1 := by
    intro h
    apply hzw
    rw [eq_inv_of_mul_eq_one_right h]
    exact (inv_eq_of_mul_eq_one_right hUz.sq).symm
  refine (stage2_of_balanced_gen hnab S.odd S.five S.inClass S.ih hbal hM hw hwB
    (le_centralizer_frame e hMz hw hJKc hJTc) hgen).2 (z * w) hx1 fun N hN => ?_
  obtain ⟨h, hh, hcomp⟩ := cfg.cover_twin S rf d hnab hΩ hno3 N hN
  refine ⟨h, ?_, hcomp⟩
  rw [mem_conjSub_iff]
  have hcomm : h * (z * w) = (z * w) * h := Subgroup.mem_centralizer_singleton_iff.mp hh
  have e1 : h⁻¹ * (z * w) * h = z * w := by
    calc h⁻¹ * (z * w) * h = h⁻¹ * ((z * w) * h) := by group
      _ = h⁻¹ * (h * (z * w)) := by rw [hcomm]
      _ = z * w := by group
  rw [e1]
  exact mul_mem hzB hwB

theorem p1RowSL4_of_twinExact (hΩall : HypOmegaModAll p f) (hAE : AEmptyTwinExact p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f)
    (hGenR : TwinYGenTOn p f (fun t n => t = .PSL ∧ n = 4))
    (hcls : TwinInvolution p f) : P1RowSL4 p f := by
  intro G _ _ _ hnab K z S hshape M hM w hw hKM hzw
  obtain ⟨-, hadm⟩ := admissible_of_localShapeT hshape (by decide : (.PSL : LTag) ≠ .trialityD4)
  have hrow : TwinRow .PSL 4 := Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
  have hL : ListedTwin .PSL 4 := Or.inr (Or.inl ⟨rfl, rfl⟩)
  exact p1_of_twin_at_row hnab S (hΩall G hnab S.odd S.five K z S.cls S.below)
    (aEmpty_of_twinExact hAE hcls hnab S hrow hL hshape) (thm7TypedBelow_of hP4 S.below) hH hGenR
    hcls hrow (NoThreeFund.of_small S.odd S.five hadm (Or.inr (Or.inl ⟨rfl, rfl⟩))) hshape hM hw
    hKM hzw

theorem p1RowSp2_of_twinExact (hΩall : HypOmegaModAll p f) (hAE : AEmptyTwinExact p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f)
    (hGenR : TwinYGenTOn p f (fun t n => t = .PSp ∧ n = 2))
    (hcls : TwinInvolution p f) : P1RowSp2 p f := by
  intro G _ _ _ hnab K z S hshape M hM w hw hKM hzw
  obtain ⟨-, hadm⟩ := admissible_of_localShapeT hshape (by decide : (.PSp : LTag) ≠ .trialityD4)
  have hrow : TwinRow .PSp 2 := Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
  have hL : ListedTwin .PSp 2 := Or.inl ⟨rfl, rfl⟩
  exact p1_of_twin_at_row hnab S (hΩall G hnab S.odd S.five K z S.cls S.below)
    (aEmpty_of_twinExact hAE hcls hnab S hrow hL hshape) (thm7TypedBelow_of hP4 S.below) hH hGenR
    hcls hrow (NoThreeFund.of_small S.odd S.five hadm (Or.inl ⟨rfl, rfl⟩)) hshape hM hw hKM hzw

theorem p1RowSU4_of_twinExact (hΩall : HypOmegaModAll p f) (hAE : AEmptyTwinExact p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f)
    (hGenR : TwinYGenTOn p f (fun t n => t = .PSU ∧ n = 4))
    (hcls : TwinInvolution p f) : P1RowSU4 p f := by
  intro G _ _ _ hnab K z S hshape M hM w hw hKM hzw
  obtain ⟨-, hadm⟩ := admissible_of_localShapeT hshape (by decide : (.PSU : LTag) ≠ .trialityD4)
  have hrow : TwinRow .PSU 4 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))))
  have hL : ListedTwin .PSU 4 := Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  exact p1_of_twin_at_row hnab S (hΩall G hnab S.odd S.five K z S.cls S.below)
    (aEmpty_of_twinExact hAE hcls hnab S hrow hL hshape) (thm7TypedBelow_of hP4 S.below) hH hGenR
    hcls hrow (NoThreeFund.of_small S.odd S.five hadm (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
    hshape hM hw hKM hzw

end Rows

end CFSG.ClassicalInvolution.Asc77
