module

public import CFSG.ClassicalInvolution.RouteD.TWEBigFrame
public import CFSG.ClassicalInvolution.Asc77.AscAETSecViol
public import CFSG.ClassicalInvolution.Asc77.AscAETWeak
public import CFSG.ClassicalInvolution.Asc77.AscT3Final
public import CFSG.ClassicalInvolution.Asc77.AscT3TypedClass
public import CFSG.ClassicalInvolution.Asc77.AscT3TypedQuot
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Section
public import CFSG.ClassicalInvolution.Asc77.WP3SCRP1Base
public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootRows
public import CFSG.ClassicalInvolution.Asc77.AscAETProved
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
public import CFSG.ClassicalInvolution.Asc77.AscT8Setup
public import CFSG.ClassicalInvolution.AschTight.Sec7L713E

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.Big

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.AscAET CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.RouteD.TwinY
open CFSG.Assembly.LowTwoRank

local notation "𝒞" => CoreAssembly.conjClass

local notation "LTag" => CFSG.Assembly.LowTwoRank.StatedLieTag

set_option linter.unusedSectionVars false

section Statement

variable (p f : ℕ) [Fact p.Prime]

@[expose] def AEmptyTwinExactB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → TwinExactShape p f K z →
        ∀ M ∈ CoreAssembly.conjClass K, AEmpty (CoreAssembly.conjClass K) M

end Statement

section Tags

variable {p f : ℕ} [Fact p.Prime]

theorem tag_ne_of_twinShapeData {X : Type} [Group X] {Φ : Set (Subgroup X)}
    {D : LieSystemData p f X Φ} (hD : TwinShapeData D) (i : Fin D.card) :
    D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4 := by
  obtain ⟨hcard, i₀, i₁, i₂, h01, h12, h02, ht₀, -, ht₂, -, hL⟩ := hD
  rcases eq_cases_of_card_three hcard h01 h12 h02 i with rfl | rfl | rfl
  · rw [ht₀]
    exact ⟨by decide, by decide⟩
  · rcases hL with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;>
      exact ⟨by decide, by decide⟩
  · rw [ht₂]
    exact ⟨by decide, by decide⟩

end Tags

section Final

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem false_of_aViol_twinShape (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {c : G}
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (D₀ : LocalLieSystemAt p f (exactFamily Ω c) c)
    (hD₀ : TwinShapeData D₀) {M J : Subgroup G} {zM zJ : G} (hM : M ∈ Ω)
    (hv : AViol Ω M J zM zJ) (hMc : c ∈ trivialOnQuot M) (hJc : c ∈ trivialOnQuot J) :
    False := by
  obtain ⟨zK, zL, hv'⟩ := exists_aViol_exactPair hp hq hΩ hc2 hM hv hMc hJc
  have hΛ : HypOmegaMod p f
      (restrictFamily (centralizingMembers (exactFamily Ω c) {c}) (exLayer Ω c)) :=
    hypOmegaMod_restrictFamily_congr (centMembers_exactFamily Ω c).symm rfl
      (hypOmegaMod_exactPair hp hq hΩ hc2)
  have hKt : M ∈ tqMembers Ω c := ⟨hM, hMc⟩
  have hKcm : exactCore c M ∈ centralizingMembers (exactFamily Ω c) {c} :=
    ⟨exactCore_mem_exactFamily hKt, exactCore_le_centralizer c M⟩
  have hKY : exactCore c M ≤ exLayer Ω c := le_centLayer hKcm
  have hK : (exactCore c M).subgroupOf (exLayer Ω c) ∈
      restrictFamily (centralizingMembers (exactFamily Ω c) {c}) (exLayer Ω c) :=
    subgroupOf_mem_restrictFamily hKcm hKY
  obtain ⟨a, hQ⟩ := T3Typed.quotViol_of_aViol hp hq hΛ hK hv'
  have hs : SecData p f c (exactFamily Ω c) :=
    secData_exactFamily hΩ.conjInvariant hΩ.classical hc2 ⟨M, hKt⟩
  let D : OmegaLie p f (secFam Ω c) := LieSystemData.toOmegaLie D₀ (omegaGen_secFam hs)
  have hΦ : HypOmegaMod p f (secFam Ω c) := hypOmegaMod_secFam hp hq hΩ hc2
  obtain ⟨i, R, S, hR, hS, hKR, hJS⟩ := T3Typed.QuotViol.exists_components D hQ
  rw [hKR, hJS] at hQ
  exact T3Typed.QuotViol.false_of_classical hp hq hΦ D (tag_ne_of_twinShapeData hD₀ i).1
    (tag_ne_of_twinShapeData hD₀ i).2 hR hS hQ

end Final


variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem exists_omegaOfSet_nonempty_of_twinExactShape (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {K : Subgroup G} {z : G} (hΩ : HypOmegaMod p f (CoreAssembly.conjClass K))
    (hz : IsClassicalMember p f K z) (hshape : TwinExactShape p f K z) :
    ∃ M ∈ CoreAssembly.conjClass K,
      (omegaOfSet (CoreAssembly.conjClass K) (twinSet (CoreAssembly.conjClass K) M)).Nonempty := by
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  obtain ⟨⟨D, hD⟩, T, hT, hcomm, hTz⟩ := hshape
  let X : XCtx p f (CoreAssembly.conjClass K) z :=
    { K := K, hK := CoreAssembly.mem_conjClass_self K, hKz := hKz, hΩ := hΩ, hp := hp2,
      hq := hq, D := D }
  obtain ⟨C, ⟨S⟩⟩ := exists_twinShapeCtx X hD hT hTz hcomm
  obtain ⟨L⟩ := C.exists_lift S
  have fd := L.frameData S
  exact ⟨L.K₁, L.hK₁, L.J, fd.hJ⟩


variable {p f : ℕ} [Fact p.Prime]

theorem aEmptyTwinExactB_proved (hΩall : HypOmegaModAll p f) : AEmptyTwinExactB p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hshape M hM
  have hΩK : HypOmegaMod p f (CoreAssembly.conjClass K) := hΩall G hnab hp2 hq K z hz hBelow
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hall : ∀ J ∈ CoreAssembly.conjClass K, ∃ g : G, conjSub g K = J := by
    rintro J ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hKz : IsUniqueInvolution K z := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  have hc2 : IsPGroup 2 (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_mul_self_eq_one hKz.sq hKz.ne_one
  have hA : AEmpty (CoreAssembly.conjClass K) K := by
    by_contra hn
    obtain ⟨J, zK, zJ, hv⟩ := not_aEmpty_iff.mp hn
    obtain ⟨M₀, hM₀, L₀, hL₀⟩ :=
      exists_omegaOfSet_nonempty_of_twinExactShape hp2 hq hΩK hz hshape
    obtain ⟨h, hh⟩ := hall L₀ hL₀.1
    have hKW : K ∈ omegaOfSet (CoreAssembly.conjClass K)
        (twinSet (CoreAssembly.conjClass K) (conjSub h⁻¹ M₀)) := by
      have := omegaOfSet_conj hΩK.conjInvariant hL₀ h⁻¹
      rwa [← hh, conjSub_inv_conjSub] at this
    have hM'Ω : conjSub h⁻¹ M₀ ∈ CoreAssembly.conjClass K := hΩK.conjInvariant h⁻¹ M₀ hM₀
    obtain ⟨g, hg⟩ := hall _ hM'Ω
    have hv' := hv.conj hΩK.conjInvariant g
    rw [hg] at hv'
    obtain ⟨J', zJ', hv'', hMc, hJc⟩ :=
      exists_weak_transfer hp2 hq hΩK hM'Ω hv' hKW hKz
    obtain ⟨D₀, hD₀⟩ := hshape.1
    exact false_of_aViol_twinShape hp2 hq hΩK hc2 D₀ hD₀ hM'Ω hv'' hMc hJc
  exact aEmpty_forall_of_transitive' hΩK.conjInvariant hall hA M hM


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
theorem exists_twinShapeData_of_localShapeT {tY : LTag} {nY : ℕ} (hL : BigTwin tY nY)
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

theorem aEmpty_of_twinExactB (hAE : AEmptyTwinExactB p f) (hcls : TwinInvolution p f)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    {K : Subgroup G} {z : G} (S : RouteDSetup p f K z) {tY : LTag} {nY : ℕ}
    (hrow : TwinRow tY nY) (hL : BigTwin tY nY) (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z) :
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

theorem twinRow_bigTwin {t : LTag} {n : ℕ} (h : TwinRow t n) : BigTwin t n := by
  rcases h with ⟨-, rfl, hn⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, hn⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, hn⟩ |
    ⟨-, rfl, rfl⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hn⟩))))
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hn⟩)))
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hn⟩))))
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))

theorem aEmptyTwinRow_proved (hΩall : HypOmegaModAll p f) (hcls : TwinInvolution p f) :
    AEmptyTwinRow p f :=
  fun _ _ _ _ hnab _ _ S _ _ hrow hshape =>
    aEmpty_of_twinExactB (aEmptyTwinExactB_proved hΩall) hcls hnab S hrow (twinRow_bigTwin hrow)
      hshape

end Rows

end CFSG.ClassicalInvolution.RouteD.TWE.Big
