module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Hyp

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped commutatorElement

section Layer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {A : Subgroup G}

theorem rLayerSub_le_centralizer_A (Ω : Set (Subgroup G)) (A : Subgroup G) :
    rLayerSub Ω A ≤ Subgroup.centralizer (A : Set G) :=
  iSup₂_le fun _ _ => iSup_le fun h => h

theorem core_le_rLayerSub {J : Subgroup G} (hJ : J ∈ Ω)
    (hJC : ∃ P : Subgroup G, IsSylow2In P J ∧ P ≤ Subgroup.centralizer (A : Set G)) :
    tightCore (J ⊓ Subgroup.centralizer (A : Set G)) ≤ rLayerSub Ω A := by
  unfold tightCore
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  have hxK : x ∈ tightCore (J ⊓ Subgroup.centralizer (A : Set G)) := Subgroup.subset_closure hx
  obtain ⟨P, hP, hxP⟩ := IsSylow2In.exists_ge (T := Subgroup.zpowers x)
    (P := tightCore (J ⊓ Subgroup.centralizer (A : Set G))) hx.2 (Subgroup.zpowers_le.mpr hxK)
  have hPJ := (isSylow2In_core_iff hJC).mp hP
  have hle : P ≤ rLayerSub Ω A := by
    unfold rLayerSub
    exact le_iSup₂_of_le P (mem_RSet_of_isSylow2In hJ hPJ.1)
      (le_iSup (fun _ : P ≤ Subgroup.centralizer (A : Set G) => P) hPJ.2)
  exact hle (hxP (Subgroup.mem_zpowers x))

@[expose] def coreFamX (Ω : Set (Subgroup G)) (A : Subgroup G) :
    Set (Subgroup ↥(rLayerSub Ω A)) :=
  restrictFamily (coreFam Ω (Subgroup.centralizer (A : Set G))) (rLayerSub Ω A)

@[expose] def secFamA (Ω : Set (Subgroup G)) (A : Subgroup G) :
    Set (Subgroup (SecQuot (rLayerSub Ω A))) :=
  quotFamily (coreFamX Ω A) (classicalInvolutionOddCore ↥(rLayerSub Ω A))

theorem hypOmegaGen_coreFamX (hΩ : HypOmegaGen Ω) : HypOmegaGen (coreFamX Ω A) := by
  refine ((clauses_coreFam hΩ (Subgroup.centralizer (A : Set G))).restrict
    (rLayerSub Ω A)).hypOmegaGen ?_
  rintro n _ ⟨L, ⟨J, hJ, ⟨P, hP, hPC⟩, rfl⟩, hLX, rfl⟩
  have hnC : (n : G) ∈ Subgroup.centralizer (A : Set G) :=
    rLayerSub_le_centralizer_A Ω A n.2
  have e1 : conjSub (n : G) (tightCore (J ⊓ Subgroup.centralizer (A : Set G))) =
      tightCore (conjSub (n : G) J ⊓ Subgroup.centralizer (A : Set G)) := by
    rw [conjSub_tightCore, conjSub_inf, conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hnC)]
  have hPn : conjSub (n : G) P ≤ Subgroup.centralizer (A : Set G) := by
    have := conjSub_mono (n := (n : G)) hPC
    rwa [conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hnC)] at this
  refine ⟨conjSub (n : G) (tightCore (J ⊓ Subgroup.centralizer (A : Set G))),
    ⟨conjSub (n : G) J, hΩ.conjInvariant _ _ hJ, ⟨conjSub (n : G) P, hP.conj _, hPn⟩, e1⟩, ?_,
    conjSub_subgroupOf _ n _⟩
  have := conjSub_mono (n := (n : G)) hLX
  rwa [conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer n.2)] at this

theorem hypOmegaGen_secFamA (hΩ : HypOmegaGen Ω) : HypOmegaGen (secFamA Ω A) :=
  TwinEdge.hypOmegaGen_quotFamily_odd (hypOmegaGen_coreFamX hΩ)
    (CFSG.ComponentClassification.OddCore.odd_card ↥(rLayerSub Ω A))

theorem aEmpty_coreFamX (hΩ : HypOmegaGen Ω) (hA : ∀ M ∈ Ω, AEmpty Ω M) (hA2 : IsPGroup 2 ↥A)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M)) :
    ∀ L ∈ coreFamX Ω A, AEmpty (coreFamX Ω A) L :=
  aEmpty_restrict_coreFam hΩ hA (nbrCore_centralizer hΩ hA2 h2) (rLayerSub_le_centralizer_A Ω A)
    (fun _ hJ hJC => core_le_rLayerSub hJ hJC) (hypOmegaGen_coreFamX hΩ)

theorem aEmpty_secFamA (hΩ : HypOmegaGen Ω) (hA : ∀ M ∈ Ω, AEmpty Ω M) (hA2 : IsPGroup 2 ↥A)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M)) :
    ∀ M ∈ secFamA Ω A, AEmpty (secFamA Ω A) M :=
  TwinADescent2.aEmpty_quotFamily_gen (hypOmegaGen_coreFamX hΩ) (hypOmegaGen_secFamA hΩ)
    (CFSG.ComponentClassification.OddCore.odd_card ↥(rLayerSub Ω A)) (aEmpty_coreFamX hΩ hA hA2 h2)

theorem secFamA_q8
    (hq : ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M → Nonempty (↥P ≃* QuaternionGroup 2)) :
    ∀ J ∈ secFamA Ω A, ∀ P : Subgroup (SecQuot (rLayerSub Ω A)), IsSylow2In P J →
      Nonempty (↥P ≃* QuaternionGroup 2) := by
  intro J hJ
  apply TwinDisc.forall_sylow_iso_of_exists
  refine TwinThmE.q8_quot_odd (CFSG.ComponentClassification.OddCore.odd_card ↥(rLayerSub Ω A))
    ?_ J hJ
  rintro _ ⟨_, ⟨M, hM, hMC, rfl⟩, hMX, rfl⟩
  obtain ⟨P, hP, hPC⟩ := hMC
  have hPs : IsSylow2In P (tightCore (M ⊓ Subgroup.centralizer (A : Set G))) :=
    (isSylow2In_core_iff ⟨P, hP, hPC⟩).mpr ⟨hP, hPC⟩
  obtain ⟨e⟩ := hq M hM P hP
  refine ⟨P.subgroupOf (rLayerSub Ω A), hPs.subgroupOf hMX, ⟨?_⟩⟩
  exact (Subgroup.subgroupOfEquivOfLe (hPs.1.trans hMX)).trans e

end Layer

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
