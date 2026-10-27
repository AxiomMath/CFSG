module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X13
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25E1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X11
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf7Distinct

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q8P.Asc77.P25R
  CFSG.ClassicalInvolution.Q8P.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan AEIdent)
open scoped MatrixGroups


section Typed

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem nonempty_equiv_of_mem_liftFam {Xs : Type} [Group Xs] [Finite Xs] {Δ : Set (Subgroup Xs)}
    {A : Subgroup Xs} (hA : A ∈ liftFam Δ) (hO : oddCoreOf A = ⊥) :
    Nonempty (A ≃* SL(2, ZMod 3)) := by
  obtain ⟨J, -, L, u, hL, rfl⟩ := hA
  exact hL.member_sat.nonempty_equiv_sl2
    ((Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp hO)

theorem isPGroup_actImage (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {b : G} (hb2 : b * b = 1) :
    IsPGroup 2 ↥(((cA S R R').subgroupOf (Subgroup.centralizer ({b} : Set G))).map
      (TwinDisc.secAct hyp.std.1.stand.hyp (isPGroup_zpowers_of_sq_eq_one hb2))) := by
  have hA2 : IsPGroup 2 ↥(cA S R R') := S.isPGroup'.to_le inf_le_left
  have hH2 : IsPGroup 2 ↥((cA S R R').subgroupOf (Subgroup.centralizer ({b} : Set G))) :=
    hA2.comap_subtype
  exact hH2.of_surjective ((TwinDisc.secAct hyp.std.1.stand.hyp
    (isPGroup_zpowers_of_sq_eq_one hb2)).subgroupMap _)
    ((TwinDisc.secAct hyp.std.1.stand.hyp (isPGroup_zpowers_of_sq_eq_one hb2)).subgroupMap_surjective _)

@[expose] noncomputable def actImg (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {b : G} (hb2 : b * b = 1) :
    Subgroup (MulAut (SecQ Ω b)) :=
  ((cA S R R').subgroupOf (Subgroup.centralizer ({b} : Set G))).map
    (TwinDisc.secAct hyp.std.1.stand.hyp (isPGroup_zpowers_of_sq_eq_one hb2))

theorem layerFacts_of_typed (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {b : G} (hbA : b ∈ cA S R R')
    (hb2 : b * b = 1) (hb1 : b ≠ 1) (hT : LayerTypedL Ω b) : LayerFacts hyp hb2 := by
  classical
  have hΩ : HypOmegaGen Ω := hyp.std.1.stand.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers b) := isPGroup_zpowers_of_sq_eq_one hb2
  have hzb : z ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hyp.hzS b hbA.1).symm
  have hzA : z ∈ cA S R R' := (z_facts hyp).1
  have hS := layer_q8Section hyp hb2
  have hconj : ∀ J ∈ liftFam (TwinDisc.secFam Ω b), ∀ y : SecQ Ω b,
      conjSub y J ∈ liftFam (TwinDisc.secFam Ω b) :=
    fun J hJ y => conjInvariant_liftFam hS.hyp.conjInvariant y J hJ
  have hP2 := isPGroup_actImage hyp hb2
  rcases hT with ⟨hno, hL⟩ | hae
  · obtain ⟨htC, htY, hu₁C, hu₁Y, hu₂C, hu₂Y, A, A', htw, hAK, hAK'⟩ :=
      EndL.layer_twinData hyp hb2 hb1 hbA hno
    have hcz : MulAut.conj (QuotientGroup.mk (⟨⟨z, htC⟩, htY⟩ : ↥(TwinDisc.coreHull Ω b)) : SecQ Ω b) ∈
        actImg hyp hb2 :=
      ⟨⟨z, hzb⟩, Subgroup.mem_subgroupOf.mpr hzA, TwinDisc.secAct_of_mem hΩ hc2 htY⟩
    rcases hL with ⟨D, hD1, i, hi⟩ | ⟨D, hD1, i, hi⟩
    · have hLT := CFSG.ClassicalInvolution.Q3.Q3T7P25.layerTwinFactsFive3_proved D hD1 ⟨i, hi⟩ htw
      obtain ⟨eA⟩ := nonempty_equiv_of_mem_liftFam htw.hA hLT.2.1
      obtain ⟨eA'⟩ := nonempty_equiv_of_mem_liftFam htw.hA' hLT.2.2.1
      have hPfix : ∀ β ∈ actImg hyp hb2, (∀ y ∈ A, β y = y) ∧ ∀ y ∈ A', β y = y := by
        rintro _ ⟨⟨x, hxb⟩, hx, rfl⟩
        exact secAct_fix_lifts hyp hb2 hb1 hbA hno hAK hAK' htw.hA htw.hA' eA eA'
          (Subgroup.mem_subgroupOf.mp hx) hxb
      exact layerFacts_of_secFacts hyp hb2 htC htY
        (secFacts_five D hD1 ⟨i, hi⟩ htw hconj hPfix).1
    · have hπ : (!piSign 3 1) = true := by decide
      have hi' : ∃ i : Fin D.card, IsOrthTag 6 (!piSign 3 1) (D.tag i) (D.rank i) :=
        ⟨i, by rw [hπ]; exact hi⟩
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hLT := CFSG.ClassicalInvolution.Asc77.CX.layer6Twin_proved 3 1 _ _ D A A' _ _ _ hD1 hi' htw
      obtain ⟨eA⟩ := nonempty_equiv_of_mem_liftFam htw.hA hLT.2.1
      obtain ⟨eA'⟩ := nonempty_equiv_of_mem_liftFam htw.hA' hLT.2.2.1
      have hPfix : ∀ β ∈ actImg hyp hb2, (∀ y ∈ A, β y = y) ∧ ∀ y ∈ A', β y = y := by
        rintro _ ⟨⟨x, hxb⟩, hx, rfl⟩
        exact secAct_fix_lifts hyp hb2 hb1 hbA hno hAK hAK' htw.hA htw.hA' eA eA'
          (Subgroup.mem_subgroupOf.mp hx) hxb
      exact layerFacts_of_secFacts hyp hb2 htC htY
        (secFacts_six D hD1 hi' htw hconj hP2 hcz hPfix eA)
  · obtain ⟨I, hker⟩ := hae
    obtain ⟨hKtq, hK'tq, hz, hz', -, -⟩ := layer_twins_tq hyp hbA
    obtain ⟨htC, htY, hzbar⟩ := isUniqueInvolution_secImg hΩ hc2 hKtq hz
    obtain ⟨htC', htY', hzbar'⟩ := isUniqueInvolution_secImg hΩ hc2 hK'tq hz'
    have hne : TwinDisc.secImg Ω b K ≠ TwinDisc.secImg Ω b K' :=
      TwinPerpV3.secImg_ne_of_twin hΩ hc2 hKtq hK'tq hyp.std.1.hne.symm hz hz'
    have F := TwinDisc.AE5.q8Fam_of_aeIdent_n (le_refl 5) hS I
    have h2' := F.two
    have hperm : ∀ β ∈ actImg hyp hb2, ∀ L ∈ TwinDisc.secFam Ω b, ∃ L' ∈ TwinDisc.secFam Ω b,
        L.map β.toMonoidHom = L' := by
      rintro _ ⟨⟨x, hxb⟩, hx, rfl⟩ L hL
      obtain ⟨J₁, hJ₁, rfl⟩ := TwinDisc.exists_of_mem_secFam hL
      exact ⟨_, TwinDisc.secImg_mem_secFam (conjSub_mem_tqMembers3 hΩ.conjInvariant hxb hJ₁),
        TwinDisc.secAct_map_secImg hΩ hc2 ⟨x, hxb⟩⟩
    have hfixK : ∀ β ∈ actImg hyp hb2, ∀ y ∈ TwinDisc.secImg Ω b K, β y = y := by
      rintro _ ⟨⟨x, hxb⟩, hx, rfl⟩
      exact TwinDisc.secAct_fix_secImg hΩ hc2 (h2' _ (TwinDisc.secImg_mem_secFam hKtq)) hxb
        (mem_trivialOnQuot_of_mem_A hyp (Subgroup.mem_subgroupOf.mp hx)).1
    have hfixK' : ∀ β ∈ actImg hyp hb2, ∀ y ∈ TwinDisc.secImg Ω b K', β y = y := by
      rintro _ ⟨⟨x, hxb⟩, hx, rfl⟩
      exact TwinDisc.secAct_fix_secImg hΩ hc2 (h2' _ (TwinDisc.secImg_mem_secFam hK'tq)) hxb
        (mem_trivialOnQuot_of_mem_A hyp (Subgroup.mem_subgroupOf.mp hx)).2
    exact layerFacts_of_secFacts hyp hb2 htC htY
      (secFacts_ae5 hS I hker (TwinDisc.secImg_mem_secFam hKtq) (TwinDisc.secImg_mem_secFam hK'tq)
        hne hzbar hzbar' hperm hfixK hfixK').1

theorem qtf_of_typedL (hty : P25_TypedL) : P25X_QTF := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp b hbA hb2 hb1 hbad
  exact layerFacts_of_typed hyp hbA hb2 hb1
    (hty G Ω K K' W S R R' z t u₁ u₂ hyp b hbA hb2 hb1 hbad)

end Typed

end CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X
