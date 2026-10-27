module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.EndDataDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LemmaD
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LeavesR
public import CFSG.LocalAnalysis.OddStandard.RouteWBalanced
public import CFSG.GH74.Generic.BProg.B2.L2Cover

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint

theorem false_of_alternating (hAlt : CFSG.OddStandard.AltStdCyclicBalancedFalse)
    (hTwoAn : TwoAnSL25) (hI : Phase1Inputs) (hA7 : TwoA7RankOne) {G : Type} [Group G]
    [Finite G] {x : G} {Y : Subgroup G} (hY : EndData G x Y) {n : ℕ} (hn : 8 ≤ n)
    (e : Nonempty (↥Y ⧸ center ↥Y ≃* alternatingGroup (Fin n)))
    (S : Sylow 2 ↥(Subgroup.centralizer (Y : Set G)))
    (hS : IsCyclic ↥(S : Subgroup ↥(Subgroup.centralizer (Y : Set G)))) : False := by
  haveI := hY.setting.simple
  obtain ⟨eA⟩ := e
  by_cases hZ : center ↥Y = ⊥
  ·
    let eY : ↥Y ≃* alternatingGroup (Fin n) :=
      (QuotientGroup.quotientBot (G := ↥Y)).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hZ.symm).trans eA)
    exact hAlt G Y hY.standardSetting n hn ⟨eY⟩ S hS hY.setting.balanced
  ·
    have hcard_dvd : Nat.card (center ↥Y) ∣ 2 := by
      have h1 := CFSG.GH74.Generic.BProg.B2.L2Cover.card_center_dvd_card_hopfMultiplier_qs
        hY.isQuasisimple eA
      have h2 := (hI.schur n (by omega)).2
      rw [h2, if_neg (by omega : ¬ (n = 6 ∨ n = 7))] at h1
      exact h1
    have hne1 : Nat.card (center ↥Y) ≠ 1 := fun h =>
      hZ (Subgroup.eq_bot_of_card_eq (center ↥Y) h)
    have hcard2 : Nat.card (center ↥Y) = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hcard_dvd with h | h
      · exact absurd h hne1
      · exact h
    have hDC : GH74.GLS.IsDoubleCoverOfAlt ↥Y n := ⟨hY.isQuasisimple, hcard2, ⟨eA⟩⟩
    obtain ⟨N, hZN, hSL⟩ := hTwoAn ↥Y n (by omega) hDC
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ
    let z : ↥Y := a
    have hzcenter : z ∈ center ↥Y := a.2
    have hz_ne : z ≠ 1 := by
      intro h
      exact ha (Subtype.ext (by simpa [z] using h))
    have horder2 : orderOf z = 2 := by
      have hdvd : orderOf z ∣ Nat.card (center ↥Y) :=
        Subgroup.orderOf_dvd_natCard (center ↥Y) hzcenter
      have hdvd2 : orderOf z ∣ 2 := by rw [hcard2] at hdvd; exact hdvd
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hz_ne
      · exact h
    have hzN : z ∈ N := hZN hzcenter
    have hbot : pPrimeCore 2 ↥Y = ⊥ := by
      rw [← oddCore_eq_pPrimeCore_two ↥Y]
      exact hY.oddCore_eq_bot
    haveI : (pPrimeCore 2 ↥Y).Normal := CFSG.pPrimeCore_normal
    have hTypU : TypU ↥Y := by
      refine Or.inr (Or.inr (Or.inr ⟨n, by omega, ?_⟩))
      exact isDoubleCoverOfAlt_of_mulEquiv
        ((QuotientGroup.quotientBot (G := ↥Y)).symm.trans
          (QuotientGroup.quotientMulEquivOfEq hbot).symm) hDC
    have hdat : CentralDatum ↥Y :=
      ⟨5, N, z, ⟨2, rfl⟩, le_refl 5, horder2, hzcenter, hzN, hSL, hTypU⟩
    exact false_of_centralDatum hI hA7 G hY.setting.nonab hY.setting.kProper hY.setting.notCat
      x Y hY.ox hY.comp hdat

end CFSG.OddStandard.SmallF3.HypA2
