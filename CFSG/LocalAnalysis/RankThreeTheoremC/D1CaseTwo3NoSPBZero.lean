module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3NoSPDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3SPResidues

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoData3.allOutEV (hS : D1CaseTwoShape G) (hd : D1CaseTwoData3 p P M H R Rbar)
    (hnosp : D1CaseTwoNoSP p M H R)
    (hout : ∀ z : H, D1CaseTwoCand p M H R z → D1CzOutside p (z : G)) :
    D1CaseTwoAllOutEV p M H R := by
  intro z hz
  obtain ⟨L, hL, hLX, hzR, hzp, hRz, hzL⟩ := id hz
  have hnSP := hnosp L hL hLX z hzR hzp hRz hzL
  have hshape := hS p P M H R Rbar hd z hz hnSP (hout z hz)
  obtain ⟨hB0, hne, hev⟩ := D1ComponentConfig3.b0_of_shape3 hd.cfg hzp hzR hRz
    (hd.cfg.centralizer_not_le hLX z.2 hzp hzL) hshape
    (hnTQ_of_not_central (hd.noCentral z hz))
  exact ⟨hout z hz, hB0, hne, hev⟩

theorem d1CaseTwoPosZeroNoSP_of {G : Type} [Group G] [Finite G] (hS : D1CaseTwoShape G)
    (hEV : D1CaseTwoPosZeroEV G)
    (hIn : D1CaseTwoPosZeroIn G) : D1CaseTwoPosZeroNoSP G := by
  intro p P M H R Rbar hd hnosp hU h0
  by_cases h : ∃ z : H, D1CaseTwoCand p M H R z ∧ ¬ D1CzOutside p (z : G)
  · exact hIn p P M H R Rbar hd hnosp h hU h0
  · push Not at h
    exact hEV p P M H R Rbar hd hnosp (D1CaseTwoData3.allOutEV hS hd hnosp h) hU h0

theorem d1CaseTwoNTwoAResNoSP_of {G : Type} [Group G] [Finite G] (hS : D1CaseTwoShape G)
    (hEV : D1CaseTwoNTwoAResEV G)
    (hIn : D1CaseTwoNTwoAResIn G) : D1CaseTwoNTwoAResNoSP G := by
  intro p P M H R Rbar hd hnosp hU L₁ L₂ h1 h2 h3 h4 h5 h6
  by_cases h : ∃ z : H, D1CaseTwoCand p M H R z ∧ ¬ D1CzOutside p (z : G)
  · exact hIn p P M H R Rbar hd hnosp h hU L₁ L₂ h1 h2 h3 h4 h5 h6
  · push Not at h
    exact hEV p P M H R Rbar hd hnosp (D1CaseTwoData3.allOutEV hS hd hnosp h) hU L₁ L₂ h1 h2
      h3 h4 h5 h6

theorem d1CaseTwoZZThreeNoSP_of {G : Type} [Group G] [Finite G] (hS : D1CaseTwoShape G)
    (hEV : D1CaseTwoZZThreeEV G)
    (hIn : D1CaseTwoZZThreeIn G) : D1CaseTwoZZThreeNoSP G := by
  intro P M H R Rbar hd hnosp hU L₁ h1 h2 h3 h4 h5 z h6 h7 h8 h9
  by_cases h : ∃ z : H, D1CaseTwoCand 3 M H R z ∧ ¬ D1CzOutside 3 (z : G)
  · exact hIn P M H R Rbar hd hnosp h hU L₁ h1 h2 h3 h4 h5 z h6 h7 h8 h9
  · push Not at h
    exact hEV P M H R Rbar hd hnosp (D1CaseTwoData3.allOutEV hS hd hnosp h) hU L₁ h1 h2 h3 h4
      h5 z h6 h7 h8 h9

end CFSG.LocalAnalysis.RankThreeTheoremC
