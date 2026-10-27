module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent2Quot
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescentSec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecBridge
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecQuot

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent2

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

section Main

variable {Y : Type} [Group Y] [Finite Y]

theorem aEmpty_sectionH' {K₀ : Subgroup Y} (hΩ : HypOmegaGen (CoreAssembly.conjClass K₀))
    (hA : AEmpty (CoreAssembly.conjClass K₀) K₀) {c : Y}
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hcK : c ∈ trivialOnQuot K₀) :
    AEmpty (CoreAssembly.conjClass ((tightCore (K₀.subgroupOf (Subgroup.centralizer ({c} : Set Y)))).subgroupOf (secH K₀ c)))
      ((tightCore (K₀.subgroupOf (Subgroup.centralizer ({c} : Set Y)))).subgroupOf (secH K₀ c)) := by
  have hAall : ∀ M ∈ CoreAssembly.conjClass K₀, AEmpty (CoreAssembly.conjClass K₀) M := by
    rintro _ ⟨g, rfl⟩
    exact aEmpty_conj hΩ.conjInvariant hA g
  have hK₀tq : K₀ ∈ tqMembers3 (CoreAssembly.conjClass K₀) c :=
    ⟨CoreAssembly.mem_conjClass_self K₀, hcK⟩
  have hΛ := TwinADescent.hypOmegaGen_coreFamily hΩ hc2
  have hK₁ : tightCore (K₀.subgroupOf (Subgroup.centralizer ({c} : Set Y))) =
      (TwinADescent.coreAt c K₀).subgroupOf (Subgroup.centralizer ({c} : Set Y)) := by
    have e : K₀.subgroupOf (Subgroup.centralizer ({c} : Set Y)) =
        (K₀ ⊓ Subgroup.centralizer ({c} : Set Y)).subgroupOf (Subgroup.centralizer ({c} : Set Y)) := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [e, tightCore_subgroupOf inf_le_right]
    rfl
  have hAΛ : AEmpty (restrictFamily (TwinADescent.coreFamily (CoreAssembly.conjClass K₀) c)
      (Subgroup.centralizer ({c} : Set Y)))
      (tightCore (K₀.subgroupOf (Subgroup.centralizer ({c} : Set Y)))) := by
    rw [hK₁]
    exact TwinADescent.aEmpty_coreFamily hΩ hΛ hAall hc2 _
      ⟨TwinADescent.coreAt c K₀, TwinADescent.coreAt_mem_coreFamily hK₀tq, TwinADescent.coreAt_le_centralizer c K₀, rfl⟩
  have hKH : tightCore (K₀.subgroupOf (Subgroup.centralizer ({c} : Set Y))) ≤ secH K₀ c :=
    le_subnormalClosure _
  set P : Set (Subgroup ↥(Subgroup.centralizer ({c} : Set Y))) :=
    {L | ∃ h : ↥(secH K₀ c), L = conjSub (h : ↥(Subgroup.centralizer ({c} : Set Y)))
      (tightCore (K₀.subgroupOf (Subgroup.centralizer ({c} : Set Y))))} with hPdef
  have hPΛ : P ⊆ restrictFamily (TwinADescent.coreFamily (CoreAssembly.conjClass K₀) c)
      (Subgroup.centralizer ({c} : Set Y)) := by
    rintro _ ⟨h, rfl⟩
    have hhc : ((h : ↥(Subgroup.centralizer ({c} : Set Y))) : Y) ∈
        Subgroup.centralizer ({c} : Set Y) := (h : ↥(Subgroup.centralizer ({c} : Set Y))).2
    have hmem : conjSub (((h : ↥(Subgroup.centralizer ({c} : Set Y))) : Y)) (TwinADescent.coreAt c K₀) ∈
        TwinADescent.coreFamily (CoreAssembly.conjClass K₀) c := by
      refine ⟨conjSub (((h : ↥(Subgroup.centralizer ({c} : Set Y))) : Y)) K₀,
        conjSub_mem_tqMembers3 hΩ.conjInvariant hhc hK₀tq, TwinADescent.conjSub_coreAt hhc K₀⟩
    have hle : conjSub (((h : ↥(Subgroup.centralizer ({c} : Set Y))) : Y)) (TwinADescent.coreAt c K₀) ≤
        Subgroup.centralizer ({c} : Set Y) := by
      have := conjSub_mono (n := (((h : ↥(Subgroup.centralizer ({c} : Set Y))) : Y)))
        (TwinADescent.coreAt_le_centralizer c K₀)
      rwa [conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hhc)] at this
    refine ⟨_, hmem, hle, ?_⟩
    rw [hK₁, conjSub_subgroupOf]
  have h1 := Thm4Twin.aEmpty_restrict hΛ hPΛ hKH hAΛ
  have hfam : restrictFamily P (secH K₀ c) = CoreAssembly.conjClass
      ((tightCore (K₀.subgroupOf (Subgroup.centralizer ({c} : Set Y)))).subgroupOf (secH K₀ c)) := by
    ext L
    constructor
    · rintro ⟨_, ⟨h, rfl⟩, hLH, rfl⟩
      exact ⟨h, conjSub_subgroupOf (secH K₀ c) h _⟩
    · rintro ⟨h, rfl⟩
      have hle : conjSub (h : ↥(Subgroup.centralizer ({c} : Set Y)))
          (tightCore (K₀.subgroupOf (Subgroup.centralizer ({c} : Set Y)))) ≤ secH K₀ c := by
        have := conjSub_mono (n := (h : ↥(Subgroup.centralizer ({c} : Set Y)))) hKH
        rwa [conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer h.2)] at this
      exact ⟨_, ⟨h, rfl⟩, hle, (conjSub_subgroupOf (secH K₀ c) h _)⟩
  rw [hfam] at h1
  exact h1

theorem aEmpty_section' {K₀ : Subgroup Y} (hΩ : HypOmegaGen (CoreAssembly.conjClass K₀))
    (hA : AEmpty (CoreAssembly.conjClass K₀) K₀) {c : Y}
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hcK : c ∈ trivialOnQuot K₀) :
    AEmpty (CoreAssembly.conjClass (tightCore (secR K₀ c))) (tightCore (secR K₀ c)) := by
  obtain ⟨P, hP, hPc⟩ := TwinADescent.exists_sylow_centralizer_of_tq hc2 hcK
  have hKH : tightCore (K₀.subgroupOf (Subgroup.centralizer ({c} : Set Y))) ≤ secH K₀ c :=
    le_subnormalClosure _
  have hΩH := TwinEdge.hypOmegaGen_sectionFamily hΩ ⟨P, hP, hPc⟩ hKH
  have hHodd : Odd (Nat.card ↥(classicalInvolutionOddCore ↥(secH K₀ c))) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥(secH K₀ c)
  have hq := TwinEdge.hypOmegaGen_quotFamily_odd hΩH hHodd
  have hAH := aEmpty_sectionH' hΩ hA hc2 hcK
  have hAallH : ∀ M ∈ CoreAssembly.conjClass
      ((tightCore (K₀.subgroupOf (Subgroup.centralizer ({c} : Set Y)))).subgroupOf (secH K₀ c)),
      AEmpty (CoreAssembly.conjClass
      ((tightCore (K₀.subgroupOf (Subgroup.centralizer ({c} : Set Y)))).subgroupOf (secH K₀ c))) M := by
    rintro _ ⟨g, rfl⟩
    exact aEmpty_conj hΩH.conjInvariant hAH g
  have hAq := TwinADescent2.aEmpty_quotFamily_gen hΩH hq hHodd hAallH
  have hmem : tightCore (secR K₀ c) ∈ quotFamily (CoreAssembly.conjClass
      ((tightCore (K₀.subgroupOf (Subgroup.centralizer ({c} : Set Y)))).subgroupOf (secH K₀ c)))
      (classicalInvolutionOddCore ↥(secH K₀ c)) :=
    ⟨_, CoreAssembly.mem_conjClass_self _, (TwinEdge.tightCore_secR K₀ c).symm⟩
  rw [TwinEdge.conjClass_tightCore_secR]
  exact hAq _ hmem

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent2
