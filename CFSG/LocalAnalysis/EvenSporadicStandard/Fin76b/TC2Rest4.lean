module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.J3

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Finkelstein77 (innAut)
open CFSG.Sporadic.Schreier (j3P j3PermEquiv)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem outer_inputs_of_sporadic
    (hOJ2 : OuterEData ↥ComponentClassification.J2Cover.Models.P) (hOJ3 : OuterEData ↥j3P)
    (hJ : IsSporadic L .J2 ∨ IsSporadic L .J3) :
    center ↥L = ⊥ ∧ center (↥L ⧸ center ↥L) = ⊥ ∧ OuterEData (↥L ⧸ center ↥L) ∧
      (innAut (↥L ⧸ center ↥L)).index ∣ 2 := by
  rcases hJ with hL | hL
  · obtain ⟨e⟩ := hL
    have hcN : center NativeSporadic.J2 = ⊥ := HypOne.center_eq_bot_of_mulEquiv
      ComponentClassification.J2Cover.nativeEquivP.symm
      ComponentClassification.J2Cover.center_P
    have hZ : center L = ⊥ := HypOne.center_eq_bot_of_mulEquiv e.symm hcN
    have hq : IsSporadic (L ⧸ center L) .J2 := isSporadic_quotient_of_center_eq_bot hZ ⟨e⟩
    obtain ⟨eq⟩ := hq
    have hcZ : center (L ⧸ center L) = ⊥ := HypOne.center_eq_bot_of_mulEquiv eq.symm hcN
    refine ⟨hZ, hcZ, hOJ2.of_mulEquiv ((MulEquiv.subgroupCongr
        ComponentClassification.J2Cover.Models.P_eq_autP).trans
          (ComponentClassification.J2Cover.nativeEquivP.symm.trans eq.symm)), ?_⟩
    exact index_dvd_two_of_mulEquiv eq hcN ComponentClassification.J2Cover.j2_mulAut_card
  · obtain ⟨e⟩ := hL
    have hcP : center j3P = ⊥ := HypOne.J3.center_j3P
    have hZ : center L = ⊥ := HypOne.center_eq_bot_of_mulEquiv (e.trans j3PermEquiv).symm hcP
    have hq : IsSporadic (L ⧸ center L) .J3 := isSporadic_quotient_of_center_eq_bot hZ ⟨e⟩
    obtain ⟨eq⟩ := hq
    have hcZ : center (L ⧸ center L) = ⊥ :=
      HypOne.center_eq_bot_of_mulEquiv (eq.trans j3PermEquiv).symm hcP
    refine ⟨hZ, hcZ, hOJ3.of_mulEquiv (j3PermEquiv.symm.trans eq.symm), ?_⟩
    obtain ⟨-, -, -, -, hAut⟩ :=
      CFSG.Sporadic.SmallOddCore.ctuc_j3_full_automorphism_permutation_model
    exact index_dvd_two_of_mulEquiv (eq.trans j3PermEquiv) hcP
      (by rw [hAut, CFSG.Sporadic.Schreier.card_j3P])

end CFSG.EvenSporadicStandard.Fin76b
