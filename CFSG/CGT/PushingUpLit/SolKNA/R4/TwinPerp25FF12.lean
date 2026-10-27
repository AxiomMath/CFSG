module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FF11
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SubnormalE2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinConnQuiet
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25F0
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FF9

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent (coreAt)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2 (imgX)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4Twin (TwinT4Hyp)
open scoped commutatorElement

section Below


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {S₁ : Sylow 2 Y} {R₁ R₂ : Subgroup Y} {t₁ u₁ u₂ b : Y}

theorem FSet.b_ne_one (F : FSet r n R S t K' W S₁ R₁ R₂ t₁ u₁ u₂ b) : b ≠ 1 := by
  rintro rfl
  obtain ⟨-, -, Q, R', hQ, -, hR', hcard⟩ := F.hF₁
  have hC : Subgroup.centralizer ({(1 : Y)} : Set Y) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact Subgroup.one_mem _
  rw [hC, inf_top_eq] at hQ
  have h1 := hQ.natCard_eq hR'
  have h2 : 0 < Nat.card ↥Q := Nat.card_pos
  omega

theorem tightInO2_ff_of_below (hr : 5 ≤ r) (hNo : NoQ16E4) (hB : Thm1RTwinBelowR (r - 1) n)
    (F : FSet r n R S t K' W S₁ R₁ R₂ t₁ u₁ u₂ b) :
    TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(Subgroup.centralizer ({b} : Set Y))) (⟨t, F.htC⟩ : ↥(Subgroup.centralizer ({b} : Set Y)))) := by
  classical
  obtain ⟨S₁', hd₁, ⟨e₁⟩⟩ := F.exists_datum
  have hbase := F.base
  have hK₁gen : tightCore ((coreAt b (tightCore R)).subgroupOf (Subgroup.centralizer ({b} : Set Y))) =
      (coreAt b (tightCore R)).subgroupOf (Subgroup.centralizer ({b} : Set Y)) := by
    have hid : tightCore (coreAt b (tightCore R)) = coreAt b (tightCore R) :=
      TwinEdge.tightCore_idem _
    have hle : tightCore (coreAt b (tightCore R)) ≤ Subgroup.centralizer ({b} : Set Y) := by
      rw [hid]
      exact TwinADescent.coreAt_le_centralizer b _
    rw [Q3.tightCore_subgroupOf hle, hid]
  obtain ⟨ht', S'', hdH, hgenH, hq8H⟩ := exists_secK hd₁ ⟨e₁⟩
  set H := subnormalClosure (tightCore ((coreAt b (tightCore R)).subgroupOf
    (Subgroup.centralizer ({b} : Set Y)))) with hH
  have hKH : (coreAt b (tightCore R)).subgroupOf (Subgroup.centralizer ({b} : Set Y)) ≤ H :=
    hK₁gen.symm.le.trans (le_subnormalClosure _)
  suffices h : TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥H)
      (⟨(⟨t, F.htC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))), ht'⟩ : ↥H)) from
    tightInO2_oddQuot_of_subnormal (isSubnormal_subnormalClosure _) ht' h
  have hT4 := F.hT4 H
  have hKbar : imgX b H (tightCore R) ∈ famF b (tightCore R) H := by
    have hX : (coreAt b (conjSub 1 (tightCore R))).subgroupOf
        (Subgroup.centralizer ({b} : Set Y)) ≤ H := by
      rw [conjSub_eq_self_of_mem (Subgroup.one_mem (tightCore R))]
      exact hKH
    have := imgX_mem_famF (K := tightCore R) (c := 1) (b := b) (X := H) (Subgroup.one_mem _) hX
    rwa [conjSub_eq_self_of_mem (Subgroup.one_mem (tightCore R))] at this
  by_cases htw : ∃ K'' ∈ twinSet (CoreAssembly.conjClass (imgX b H (tightCore R)))
      (imgX b H (tightCore R)), K'' ≠ imgX b H (tightCore R)
  ·
    have hHodd : Odd (Nat.card ↥(classicalInvolutionOddCore ↥H)) :=
      CFSG.ComponentClassification.OddCore.odd_card ↥H
    have hdq := TwinEdge.oddQuot hdH hHodd
    have hgenq := TwinEdge.oddQuot_selfGen (N := classicalInvolutionOddCore ↥H) hgenH
    obtain ⟨e⟩ := hq8H
    have hq8q := (TwinEdge.sylowEquiv hdH hHodd).symm.trans e
    have hOq : TightOddFree (↥H ⧸ classicalInvolutionOddCore ↥H) :=
      CFSG.ABGLocalTools.oddCore_quotient_oddCore_eq_bot
    have hbarcore : tightCore (imgX b H (tightCore R)) = imgX b H (tightCore R) :=
      hT4.tightCore_eq hKbar
    have hΩ' : HypOmegaGen (CoreAssembly.conjClass (tightCore (imgX b H (tightCore R)))) :=
      hT4.hypOmegaGen_conjClass hKbar
    have hAE' : AEmpty (CoreAssembly.conjClass (tightCore (imgX b H (tightCore R))))
        (tightCore (imgX b H (tightCore R))) := by
      rw [hbarcore]
      refine Thm4Twin.aEmpty_sub hT4.hyp ?_ (hT4.aEmpty _ hKbar)
      rintro _ ⟨g, rfl⟩
      exact hT4.hyp.conjInvariant g _ hKbar
    have htw' : ∃ K'' ∈ twinSet (CoreAssembly.conjClass (tightCore (imgX b H (tightCore R))))
        (tightCore (imgX b H (tightCore R))), K'' ≠ tightCore (imgX b H (tightCore R)) := by
      rw [hbarcore]
      exact htw
    have hlt : Nat.card (↥H ⧸ classicalInvolutionOddCore ↥H) < n := by
      have h1 : Nat.card (↥H ⧸ classicalInvolutionOddCore ↥H) ≤ Nat.card ↥H :=
        Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
      have h2 : Nat.card ↥H ≤ Nat.card ↥(Subgroup.centralizer ({b} : Set Y)) :=
        Subgroup.card_le_card_group H
      have h3 := TwinEdge.card_centralizer_lt_of_center F.hP.center_eq_bot F.b_ne_one
      rw [← F.hP.core.card]
      omega
    have hT := thm1RTwinInO2_of_below (r := r - 1) (by omega) hNo hB
    exact hT _ hlt _ _ _ hdq ⟨hq8q⟩ hgenq hOq hΩ' hAE' htw'
  · exact tightInO2_of_noTwin F hKH ht' htw

theorem zStarFFR_of_below (hr : 5 ≤ r) (hNo : NoQ16E4) (hB : Thm1RTwinBelowR (r - 1) n) :
    ZStarFFR r n := by
  intro Y _ _ R S t hP K' W S₁ R₁ R₂ t₁ u₁ u₂ hyp h11 b hbS hb2 hF₁ hF₂
  have F : FSet r n R S t K' W S₁ R₁ R₂ t₁ u₁ u₂ b := ⟨by omega, hP, hyp, h11, hbS, hb2, hF₁⟩
  exact mem_zStarOf_ff_of_inO2 hr hP hyp h11 hbS hb2 hF₁ F.htC (tightInO2_ff_of_below hr hNo hB F)

end Below

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516
