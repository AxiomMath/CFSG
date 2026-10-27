module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSec711Layer

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSec711

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE
open CFSG.CGT.PushingUpLit.SolKNA.R4.ThmE CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

section Sixeleven

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem member_inf_mem_eta (hΦ : HypOmegaGen Φ) {η : Set (Subgroup X)} (hη : η ∈ etaG Φ)
    {S : Sylow 2 X} (hηS : ∀ U ∈ η, U ≤ (S : Subgroup X)) {N R : Subgroup X} (hN : N ∈ Φ)
    (hR : IsSylow2In R N) (hRS : R ≤ (S : Subgroup X)) : N ⊓ (⨆ U ∈ η, U) ∈ η := by
  have h8 : 8 ≤ Nat.card ↥R := Sec6Gen.eight_le_of_mem_RSet hΦ (mem_RSet_of_isSylow2In hN hR)
  have hcard : 2 < Nat.card ↥(N ⊓ (S : Subgroup X)) :=
    lt_of_lt_of_le (by omega) (h8.trans (Subgroup.card_le_of_le (le_inf hR.1 hRS)))
  exact Sec6Gen.l6_11Gen X Φ hΦ S η hη hηS N hN hcard

theorem mem_USet_of_mem_etaG {η : Set (Subgroup X)} (hη : η ∈ etaG Φ) {U : Subgroup X} (hU : U ∈ η) :
    U ∈ USet Φ := by
  obtain ⟨S₀, hS₀, -⟩ := hη
  exact (hS₀.1 hU).1

theorem normal_of_conj_eq {V : Subgroup X} (hV : ∀ x : X, conjSub x V = V) : V.Normal := by
  refine ⟨fun n hn g => ?_⟩
  have h1 : g * n * g⁻¹ ∈ conjSub g V := conj_mem_conjSub hn
  rwa [hV g] at h1

end Sixeleven



section Cor

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {u : G}

theorem mem_secD_of_normal (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers u))
    {W : Subgroup G} (hW : W ∈ WSet Ω) (huW : u ∈ W)
    {V : Subgroup (↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u))}
    (hV : V ∈ WSet (TwinDisc.secFam Ω u)) (hVn : ∀ x, conjSub x V = V) :
    ∀ N ∈ TwinDisc.secFam Ω u, N ∈ secD Ω W u := by
  classical
  obtain ⟨Pb, hlayer⟩ := layer hΩ hc2 hW huW
  have hΦ : HypOmegaGen (TwinDisc.secFam Ω u) := hypOmegaGen_secFam hΩ hc2
  intro N hN
  obtain ⟨η, hη, rfl⟩ := id hV
  have hV2 : IsPGroup 2 ↥(⨆ U ∈ η, U) := isPGroup_of_mem_WSet hV
  haveI : (⨆ U ∈ η, U).Normal := normal_of_conj_eq hVn
  have hVPb : (⨆ U ∈ η, U) ≤ (Pb : Subgroup _) := hV2.le_sylow_of_normal Pb
  obtain ⟨R, hR, -⟩ := IsSylow2In.exists_ge (T := ⊥) IsPGroup.of_bot (bot_le : ⊥ ≤ N)
  obtain ⟨S', hS'⟩ := hR.2.1.exists_le_sylow
  have hVS' : ∀ U ∈ η, U ≤ (S' : Subgroup _) := fun U hU =>
    (le_iSup₂ (f := fun U (_ : U ∈ η) => U) U hU).trans (hV2.le_sylow_of_normal S')
  have hmem := member_inf_mem_eta hΦ hη hVS' hN hR hS'
  exact hlayer (mem_USet_of_mem_etaG hη hmem) (inf_le_right.trans hVPb) hN inf_le_left

theorem exists_wgroup_dSet_le (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers u))
    {W : Subgroup G} (hW : W ∈ WSet Ω) (huW : u ∈ W) :
    ∃ V ∈ WSet (TwinDisc.secFam Ω u),
      ∀ N ∈ TwinDisc.secFam Ω u,
        ∀ R : Subgroup (↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u)),
          IsSylow2In R N → R ≤ Subgroup.normalizer (V : Set _) → N ∈ secD Ω W u := by
  classical
  obtain ⟨Pb, hlayer⟩ := layer hΩ hc2 hW huW
  have hΦ : HypOmegaGen (TwinDisc.secFam Ω u) := hypOmegaGen_secFam hΩ hc2
  obtain ⟨η, hη, hηinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hΦ Pb
  have hηG : η ∈ etaG (TwinDisc.secFam Ω u) := ⟨Pb, hη, hηinv⟩
  have hV : (⨆ U ∈ η, U) ∈ WSet (TwinDisc.secFam Ω u) := ⟨η, hηG, rfl⟩
  refine ⟨_, hV, fun N hN R hR hRn => ?_⟩
  have hV2 : IsPGroup 2 ↥(⨆ U ∈ η, U) := isPGroup_of_mem_WSet hV
  have hsup : IsPGroup 2 ↥(R ⊔ (⨆ U ∈ η, U)) := hR.2.1.to_sup_of_normal_right' hV2 hRn
  obtain ⟨S', hS'⟩ := hsup.exists_le_sylow
  have hVS' : ∀ U ∈ η, U ≤ (S' : Subgroup _) := fun U hU =>
    (le_iSup₂ (f := fun U (_ : U ∈ η) => U) U hU).trans (le_sup_right.trans hS')
  have hmem := member_inf_mem_eta hΦ hηG hVS' hN hR (le_sup_left.trans hS')
  exact hlayer (mem_USet_of_mem_etaG hηG hmem) ((hη.1 hmem).2) hN inf_le_left

end Cor

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSec711
