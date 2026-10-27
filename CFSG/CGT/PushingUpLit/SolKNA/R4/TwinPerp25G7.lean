module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FF17
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25G4
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25G5
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25G6
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinModelSp62
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinModelD42
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf14E4
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FF12

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

namespace Four

@[expose] def E4TwinFactsQ8 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q],
    (CFSG.Blueprint.LieModel Q .PSp 3 2 1 ∨ CFSG.Blueprint.LieModel Q .POmegaPlus 4 2 1) →
    ∀ w : Q, orderOf w = 2 → ¬ IsPGroup 2 ↥(Subgroup.centralizer ({w} : Set Q))

theorem oddCore_centralizer_eq_bot_of_models (Q : Type) [Group Q]
    [Finite Q]
    (hQ : CFSG.Blueprint.LieModel Q .PSp 3 2 1 ∨ CFSG.Blueprint.LieModel Q .POmegaPlus 4 2 1)
    (w : Q) (hw : orderOf w = 2) : Balance.oddCoreIn (Subgroup.centralizer ({w} : Set Q)) = ⊥ := by
  rcases hQ with hQ | hQ
  · exact TwinCentRes.modelFactSp62 Q hQ w hw
  · have := TwinCentRes.isSimple_of_pomegaPlus hQ
    exact TwinExitPf14.oddCoreIn_centralizer_eq_bot_of_autOddFree
      (TwinCentRes.modelFactD42_of_cert Q hQ) hw

theorem tightCore_subgroupOf_coreAt {Y : Type} [Group Y] [Finite Y] (b : Y) (K : Subgroup Y) :
    tightCore ((coreAt b K).subgroupOf (Subgroup.centralizer ({b} : Set Y))) =
      (coreAt b K).subgroupOf (Subgroup.centralizer ({b} : Set Y)) := by
  have hid : tightCore (coreAt b K) = coreAt b K := TwinEdge.tightCore_idem _
  have hle : tightCore (coreAt b K) ≤ Subgroup.centralizer ({b} : Set Y) := by
    rw [hid]
    exact TwinADescent.coreAt_le_centralizer b _
  rw [Q3.tightCore_subgroupOf hle, hid]

theorem conj_eq_of_comm {G : Type} [Group G] (a g : G) (h : g * a = a * g) : g * a * g⁻¹ = a := by
  rw [h]
  group

section Sec


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {S₁ : Sylow 2 Y} {R₁ R₂ : Subgroup Y} {t₁ u₁ u₂ b : Y}

theorem central_of_fSection (hE4 : E4TwinFactsQ8)
    (hP3 : TL4.TightBelowRPlus 3 n) (F : FSet 4 n R S t K' W S₁ R₁ R₂ t₁ u₁ u₂ b)
    {H : Subgroup ↥(Subgroup.centralizer ({b} : Set Y))}
    (hHeq : H = subnormalClosure (tightCore ((coreAt b (tightCore R)).subgroupOf
      (Subgroup.centralizer ({b} : Set Y)))))
    (htH : (⟨t, F.htC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))) ∈ H)
    (htw : ∃ K'' ∈ twinSet (CoreAssembly.conjClass (imgX b H (tightCore R))) (imgX b H (tightCore R)),
      K'' ≠ imgX b H (tightCore R)) :
    ∀ g : ↥H ⧸ classicalInvolutionOddCore ↥H,
      g * QuotientGroup.mk' (classicalInvolutionOddCore ↥H)
        (⟨(⟨t, F.htC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))), htH⟩ : ↥H) * g⁻¹ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥H)
        (⟨(⟨t, F.htC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))), htH⟩ : ↥H) := by
  classical
  subst hHeq
  obtain ⟨S₁', hd₁, ⟨e₁⟩⟩ := F.exists_datum
  have hbase := F.base
  obtain ⟨ht', S'', hdH, hgenH, hq8H⟩ := exists_secK hd₁ ⟨e₁⟩
  set H := subnormalClosure (tightCore ((coreAt b (tightCore R)).subgroupOf
    (Subgroup.centralizer ({b} : Set Y)))) with hH
  have hK₁gen := tightCore_subgroupOf_coreAt b (tightCore R)
  have hKH : (coreAt b (tightCore R)).subgroupOf (Subgroup.centralizer ({b} : Set Y)) ≤ H :=
    hK₁gen.symm.le.trans (le_subnormalClosure _)
  have hHsub : IsSubnormal H ⊤ := isSubnormal_subnormalClosure _
  have hT4 := F.hT4 H
  have hKbar : imgX b H (tightCore R) ∈ famF b (tightCore R) H := by
    have hX : (coreAt b (conjSub 1 (tightCore R))).subgroupOf
        (Subgroup.centralizer ({b} : Set Y)) ≤ H := by
      rw [conjSub_eq_self_of_mem (Subgroup.one_mem (tightCore R))]
      exact hKH
    have := imgX_mem_famF (K := tightCore R) (c := 1) (b := b) (X := H) (Subgroup.one_mem _) hX
    rwa [conjSub_eq_self_of_mem (Subgroup.one_mem (tightCore R))] at this
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
  have hOut := (hP3.twin rfl) _ hlt _ _ _ hdq ⟨hq8q⟩ hgenq hOq hΩ' hAE' htw'
  have hD : TC.Thin.ThmDAbsAt 3 (↥H ⧸ classicalInvolutionOddCore ↥H) := hP3.thmD.d2 _ hlt
  have hu : IsUniqueInvolution (imgX b H (tightCore R))
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (⟨(⟨t, F.htC⟩ : ↥(Subgroup.centralizer
        ({b} : Set Y))), htH⟩ : ↥H)) :=
    isUniqueInvolution_imgF_X hT4 hKbar hbase.inv_core F.htC htH
  have hΩ'' : HypOmegaGen (CoreAssembly.conjClass (imgX b H (tightCore R))) := by
    rw [hbarcore] at hΩ'
    exact hΩ'
  have hAE'' : AEmpty (CoreAssembly.conjClass (imgX b H (tightCore R))) (imgX b H (tightCore R)) := by
    rw [hbarcore] at hAE'
    exact hAE'
  have hS : Q8Sec (↥H ⧸ classicalInvolutionOddCore ↥H) (imgX b H (tightCore R))
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (⟨(⟨t, F.htC⟩ : ↥(Subgroup.centralizer
        ({b} : Set Y))), htH⟩ : ↥H)) := by
    refine ⟨hΩ'', hu, hbarcore, ?_, hOq, ?_, ?_, htw⟩
    · have h1 : (⨆ g : ↥H ⧸ classicalInvolutionOddCore ↥H,
          conjSub g (tightCore (imgX b H (tightCore R)))) = ⊤ := hgenq
      rw [hbarcore] at h1
      exact h1
    · rintro _ ⟨g, rfl⟩
      exact aEmpty_conj hΩ''.conjInvariant hAE'' g
    · rintro _ ⟨g, rfl⟩ P hP
      exact hT4.quat _ (hT4.hyp.conjInvariant g _ hKbar) P hP
  have hcent := central_of_sec hS (oddEC_quot F htH) (noCentFour_quot F hHsub htH) hD
    (fun Q _ _ hQ w hw => oddCore_centralizer_eq_bot_of_models Q hQ w hw)
    (fun Q _ _ hQ w hw => hE4 Q hQ w hw) hOut
  intro g
  exact conj_eq_of_comm _ g (hcent g)

end Sec

end Four

section Final



theorem twinCentral4_of_facts (hE4 : Four.E4TwinFactsQ8) (n : ℕ) :
    TwinCentral4 n := by
  intro hP3 Y _ _ R S t K' W S₁ R₁ R₂ t₁ u₁ u₂ b F htH htw g
  refine Four.central_of_fSection hE4 hP3 F ?_ htH htw g
  unfold fSection
  rw [Four.tightCore_subgroupOf_coreAt]


end Final

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516
