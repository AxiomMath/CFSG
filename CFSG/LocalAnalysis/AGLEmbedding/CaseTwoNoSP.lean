module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPBZero
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPIdent
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPShape
import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Cz

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {z : G}
  {T : Sylow 5 (Subgroup.centralizer ({z} : Set G))} {Pbar : Sylow 5 (D1CzQuot 5 z)}
  {K : Subgroup (D1CzQuot 5 z)}

theorem D1CzReduced.false_of_mem_of_five (hc : D1CzReduced 5 M z T Pbar K) (hZ5 : KFactCenterFive)
    (hnSP : ¬ D1CzSP 5 z) (hzK : d1CzElt 5 z ∈ K) : False := by
  have hp : (5 : ℕ).Prime := hc.red.prime
  have : Fact (5 : ℕ).Prime := ⟨hp⟩
  have h3 := hc.pRank_eq_three hnSP
  have hcat := hc.catalog.isCatalogGroup_center_quotient hc.comp
  have h5 : 5 ∣ Nat.card (Subgroup.center K) := by
    have hmem : (⟨d1CzElt 5 z, hzK⟩ : K) ∈ Subgroup.center K :=
      Subgroup.mem_center_iff.mpr fun k => Subtype.ext (Subgroup.mem_center_iff.mp hc.center k)
    have h1 := Subgroup.orderOf_dvd_natCard (Subgroup.center K) hmem
    rwa [Subgroup.orderOf_mk, hc.order] at h1
  have h4 := hZ5 K hc.comp.2.2 hcat h5
  obtain ⟨TK, hTK⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Pbar
    hc.normal.isSubnormal
  have hle : Open.pRank 5 (⊤ : Subgroup K) ≤ Open.pRank 5 (Pbar : Subgroup (D1CzQuot 5 z)) := by
    rw [← (SectionRank.pRank_sylow TK).1,
      ← pRank_map_of_injective 5 hp K.subtype K.subtype_injective, hTK]
    exact pRank_mono 5 hp inf_le_left
  omega

end Cz

section Data

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M H R : Subgroup G}
  {Rbar : Sylow 5 (H ⧸ primeComplementCore (G := H) 5)}

theorem D1CaseTwoDataAt.false_of_in_five (hd : D1CaseTwoDataAt 5 P M H R Rbar) (hAut : KFactCycAut)
    (hS : KFactSeitzCyc) (hSyl : KFactCaseTwoSylow) (hZ5 : KFactCenterFive)
    (hnosp : D1CaseTwoNoSP 5 M H R)
    (hin : ∃ z : H, D1CaseTwoCand 5 M H R z ∧ ¬ D1CzOutside 5 (z : G)) : False := by
  obtain ⟨z, hz, hout⟩ := hin
  obtain ⟨L, hL, hLX, hzR, hzp, hRz, hzL⟩ := hz
  have hnSP := hnosp L hL hLX z hzR hzp hRz hzL
  obtain ⟨m, hm, T, hRT, hTP⟩ := hd.cfg.exists_sylow_centralizer hRz
  obtain ⟨Pbar, K, hc⟩ := D1CaseTwoDataAt.exists_czReduced hd hAut hS hSyl
    ⟨L, hL, hLX, hzR, hzp, hRz, hzL⟩ hm hRT hTP
  unfold D1CzOutside at hout
  push Not at hout
  obtain ⟨KC, hKC, hzKC⟩ := hout
  rw [hc.unique KC hKC] at hzKC
  exact hc.false_of_mem_of_five hZ5 hnSP hzKC

theorem D1CaseTwoData.false_of_in_five (hd : D1CaseTwoData 5 P M H R Rbar) (hβ : KFactBeta)
    (hS : KFactSeitzCyc) (hSyl : KFactCaseTwoSylow) (hZ5 : KFactCenterFive)
    (hnosp : D1CaseTwoNoSP 5 M H R)
    (hin : ∃ z : H, D1CaseTwoCand 5 M H R z ∧ ¬ D1CzOutside 5 (z : G)) : False :=
  D1CaseTwoDataAt.false_of_in_five (hd := hd.toAt) (hAut := (kFactCycAut_of_kFactBeta hβ))
    (hS := hS) (hSyl := hSyl) (hZ5 := hZ5) (hnosp := hnosp) (hin := hin)

end Data

theorem D1CaseTwoDataAt.three_or_five {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G}
    {M H R : Subgroup G} {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    (hd : D1CaseTwoDataAt p P M H R Rbar) (hAut : KFactCycAut) (hS : KFactSeitzCyc) {z : H}
    (hz : D1CaseTwoCand p M H R z) : p = 3 ∨ p = 5 := by
  obtain ⟨L, hL, hLX, -⟩ := hz
  obtain ⟨d, hd' | hd', -⟩ :=
    hd.cfg.red.isCaseTwoGroup_of_not_le_of_aut hd.cfg.catalog (hAut _ _ _ _ hd.cfg.red
        hd.cfg.catalog) hS hd.cyclic hd.rank hL hLX
  · exact Or.inl hd'.1
  · exact Or.inr hd'.1

theorem D1CaseTwoData.three_or_five {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G}
    {M H R : Subgroup G} {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    (hd : D1CaseTwoData p P M H R Rbar) (hβ : KFactBeta) (hS : KFactSeitzCyc) {z : H}
    (hz : D1CaseTwoCand p M H R z) : p = 3 ∨ p = 5 :=
  D1CaseTwoDataAt.three_or_five (hd := hd.toAt) (hAut := (kFactCycAut_of_kFactBeta hβ)) (hS := hS)
    (hz := hz)

theorem d1CaseTwoPosZeroIn_of (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hSyl : KFactCaseTwoSylow) (hZ5 : KFactCenterFive) (h3 : D1CaseTwoPosZeroInThree) :
    D1CaseTwoPosZeroIn := by
  intro G _ _ p P M H R Rbar hd hnosp hin hU h0
  obtain ⟨z, hz, -⟩ := id hin
  rcases D1CaseTwoData.three_or_five hd hβ hS hz with rfl | rfl
  · exact h3 G P M H R Rbar hd hnosp hin hU h0
  · exact D1CaseTwoData.false_of_in_five hd hβ hS hSyl hZ5 hnosp hin

theorem d1CaseTwoNTwoAResIn_of (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hSyl : KFactCaseTwoSylow) (hZ5 : KFactCenterFive) (h3 : D1CaseTwoNTwoAResInThree) :
    D1CaseTwoNTwoAResIn := by
  intro G _ _ p P M H R Rbar hd hnosp hin hU L₁ L₂ h1 h2 h3' h4 h5 h6
  obtain ⟨z, hz, -⟩ := id hin
  rcases D1CaseTwoData.three_or_five hd hβ hS hz with rfl | rfl
  · exact h3 G P M H R Rbar hd hnosp hin hU L₁ L₂ h1 h2 h3' h4 h5 h6
  · exact D1CaseTwoData.false_of_in_five hd hβ hS hSyl hZ5 hnosp hin

theorem d1CaseTwoPosZeroNoSP_of_kFacts (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hL2 : KFactCaseTwoLocal) (hInv : KFactCaseTwoInv) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (hNo2 : KFactCaseTwoNoTwo) (hEV : D1CaseTwoPosZeroEV)
    (hIn : D1CaseTwoPosZeroIn) : D1CaseTwoPosZeroNoSP :=
  d1CaseTwoPosZeroNoSP_of (d1CaseTwoShape_of hβ hS hL2 hInv hSch hSyl hNo2) hEV hIn

theorem d1CaseTwoNTwoAResNoSP_of_kFacts (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hL2 : KFactCaseTwoLocal) (hInv : KFactCaseTwoInv) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (hNo2 : KFactCaseTwoNoTwo) (hEV : D1CaseTwoNTwoAResEV)
    (hIn : D1CaseTwoNTwoAResIn) : D1CaseTwoNTwoAResNoSP :=
  d1CaseTwoNTwoAResNoSP_of (d1CaseTwoShape_of hβ hS hL2 hInv hSch hSyl hNo2) hEV hIn

theorem d1CaseTwoZZThreeNoSP_of_kFacts (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hL2 : KFactCaseTwoLocal) (hInv : KFactCaseTwoInv) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (hNo2 : KFactCaseTwoNoTwo) (hEV : D1CaseTwoZZThreeEV)
    (hIn : D1CaseTwoZZThreeIn) : D1CaseTwoZZThreeNoSP :=
  d1CaseTwoZZThreeNoSP_of (d1CaseTwoShape_of hβ hS hL2 hInv hSch hSyl hNo2) hEV hIn

theorem d1CaseTwoPosZeroNoSP_of_residues (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hL2 : KFactCaseTwoLocal) (hInv : KFactCaseTwoInv) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (hNo2 : KFactCaseTwoNoTwo) (hZ5 : KFactCenterFive)
    (hEV : D1CaseTwoPosZeroEV) (hIn : D1CaseTwoPosZeroInThree) : D1CaseTwoPosZeroNoSP :=
  d1CaseTwoPosZeroNoSP_of_kFacts hβ hS hL2 hInv hSch hSyl hNo2 hEV
    (d1CaseTwoPosZeroIn_of hβ hS hSyl hZ5 hIn)

theorem d1CaseTwoNTwoAResNoSP_of_residues (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hL2 : KFactCaseTwoLocal) (hInv : KFactCaseTwoInv) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (hNo2 : KFactCaseTwoNoTwo) (hZ5 : KFactCenterFive)
    (hEV : D1CaseTwoNTwoAResEV) (hIn : D1CaseTwoNTwoAResInThree) : D1CaseTwoNTwoAResNoSP :=
  d1CaseTwoNTwoAResNoSP_of_kFacts hβ hS hL2 hInv hSch hSyl hNo2 hEV
    (d1CaseTwoNTwoAResIn_of hβ hS hSyl hZ5 hIn)

end CFSG.AGLEmbedding
