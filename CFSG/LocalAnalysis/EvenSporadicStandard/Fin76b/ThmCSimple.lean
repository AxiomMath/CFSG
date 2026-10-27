module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Rest8
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.NotZ2A6
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.AutEFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Final2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Final4

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Finkelstein77 (innAut)
open CFSG.Sporadic.Schreier (j3P j3PermEquiv card_j3P j2P j2PermEquiv)
open CFSG.Sporadic.SmallOddCore (ctuc_j3_full_automorphism_permutation_model)

@[expose] def Fin76bThmCSimple : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L →
    (IsSporadic L .J2 ∨ IsSporadic L .J3) →
    (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    (L ⊔ centralizer (L : Set G)).relIndex (normalizer (L : Set G)) = 2 → False

section Inner

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_inner_thmCSimple (hC : Fin76bThmCSimple) (h : StdHyp G L)
    (hJ : IsSporadic L .J2 ∨ IsSporadic L .J3)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hout : (innAut (L ⧸ center L)).index ∣ 2)
    (hinner : normalizer (L : Set G) ≤ L ⊔ centralizer (L : Set G) → False) : False := by
  have hdvd := (relIndex_normalizer_dvd (G := G) h.standard.1.1).trans hout
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · exact hinner (Subgroup.relIndex_eq_one.1 h1)
  · exact hC G L h hJ hS h2

theorem j2_not_standard_of_rest₆_thmCSimple
    (hSol : SolomonZ2A6) (hC : Fin76bThmCSimple) (hR : Fin76bInnerRest₆) (h : StdHyp G L) :
    ¬ IsSporadic L .J2 := by
  intro hL
  have hL' := hL
  obtain ⟨e⟩ := hL
  have hcN : center NativeSporadic.J2 = ⊥ := HypOne.center_eq_bot_of_mulEquiv
    ComponentClassification.J2Cover.nativeEquivP.symm ComponentClassification.J2Cover.center_P
  have hZ : center L = ⊥ := HypOne.center_eq_bot_of_mulEquiv e.symm hcN
  have hq : IsSporadic (L ⧸ center L) .J2 := isSporadic_quotient_of_center_eq_bot hZ ⟨e⟩
  have hfull := HypOne.J2.fullRowData_of_isSporadic hq
  have hF := HypOne.J2.foursGroupCondition_of_isSporadic (Y := L) ⟨e⟩
  have hS := fun S => h.card_sylow_eq_two_of_fours hfull.rowData.hypothesisOne hF S
  have hout : (innAut (L ⧸ center L)).index ∣ 2 := by
    obtain ⟨eq⟩ := hq
    exact index_dvd_two_of_mulEquiv eq hcN ComponentClassification.J2Cover.j2_mulAut_card
  have hB : BetaDataSqB ↥ComponentClassification.J2Cover.Models.P :=
    BetaDataSqB.of_mulEquiv
      ((j2PermEquiv.symm.trans ComponentClassification.J2Cover.nativeEquivP).trans
        (MulEquiv.subgroupCongr ComponentClassification.J2Cover.Models.P_eq_autP.symm))
      J2.betaDataSqB_j2P
  exact false_of_inner_thmCSimple hC h (Or.inl hL') hS hout fun hinner =>
    false_of_rest₆ hSol hR h (Or.inl hL') hS hinner
      (((MulEquiv.subgroupCongr ComponentClassification.J2Cover.Models.P_eq_autP).trans
        ComponentClassification.J2Cover.nativeEquivP.symm).trans e.symm) J2.sylowEData_P hB hZ

theorem j3_not_standard_of_rest₆_thmCSimple
    (hSol : SolomonZ2A6) (hC : Fin76bThmCSimple) (hR : Fin76bInnerRest₆) (h : StdHyp G L) :
    ¬ IsSporadic L .J3 := by
  intro hL
  have hL' := hL
  obtain ⟨e⟩ := hL
  have hcP : center j3P = ⊥ := HypOne.J3.center_j3P
  have hZ : center L = ⊥ := HypOne.center_eq_bot_of_mulEquiv (e.trans j3PermEquiv).symm hcP
  have hq : IsSporadic (L ⧸ center L) .J3 := isSporadic_quotient_of_center_eq_bot hZ ⟨e⟩
  have hfull := HypOne.J3.fullRowData_of_isSporadic hq
  have hF := HypOne.J3.foursGroupCondition_of_isSporadic (Y := L) ⟨e⟩
  have hS := fun S => h.card_sylow_eq_two_of_fours hfull.rowData.hypothesisOne hF S
  have hout : (innAut (L ⧸ center L)).index ∣ 2 := by
    obtain ⟨eq⟩ := hq
    obtain ⟨-, -, -, -, hAut⟩ := ctuc_j3_full_automorphism_permutation_model
    exact index_dvd_two_of_mulEquiv (eq.trans j3PermEquiv) hcP (by rw [hAut, card_j3P])
  exact false_of_inner_thmCSimple hC h (Or.inr hL') hS hout fun hinner =>
    false_of_rest₆ hSol hR h (Or.inr hL') hS hinner (j3PermEquiv.symm.trans e.symm)
      J3.sylowEData_j3P J3.betaDataSqB_j3P hZ

end Inner

theorem j2_not_standard_of_rest₈_simple {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hSol : SolomonZ2A6) (hC : Fin76bThmCSimple) (hR : Fin76bInnerRest₈) (h : StdHyp G L) :
    ¬ IsSporadic L .J2 :=
  j2_not_standard_of_rest₆_thmCSimple hSol hC
    (fin76bInnerRest₆_of_rest₇
      (fin76bLemma65b_of_noKleinFour
        (fin76bNoKleinFour_of_swapInCentralizer
          (fin76bSwapInCentralizer_of_innerOnD_autE
            (fin76bSwapInnerOnD_of_notZ2A6 fin76bNotZ2A6) fin76bAutE)))
      (fin76bInnerRest₇_of_rest₈ fin76bNotZ2A6 fin76bBetaData fin76bWFacts hR)) h

theorem j3_not_standard_of_rest₈_simple {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hSol : SolomonZ2A6) (hC : Fin76bThmCSimple) (hR : Fin76bInnerRest₈) (h : StdHyp G L) :
    ¬ IsSporadic L .J3 :=
  j3_not_standard_of_rest₆_thmCSimple hSol hC
    (fin76bInnerRest₆_of_rest₇
      (fin76bLemma65b_of_noKleinFour
        (fin76bNoKleinFour_of_swapInCentralizer
          (fin76bSwapInCentralizer_of_innerOnD_autE
            (fin76bSwapInnerOnD_of_notZ2A6 fin76bNotZ2A6) fin76bAutE)))
      (fin76bInnerRest₇_of_rest₈ fin76bNotZ2A6 fin76bBetaData fin76bWFacts hR)) h

end CFSG.EvenSporadicStandard.Fin76b
