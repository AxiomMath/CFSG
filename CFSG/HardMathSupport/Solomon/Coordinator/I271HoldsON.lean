module

public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsGen
public import CFSG.HardMathSupport.Solomon.Coordinator.ON25Holds
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCSylowUM
public import CFSG.HardMathSupport.Solomon.Coordinator.I27_1Fam
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCOut

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Solomon.UniquenessMaximal

section ONLow



set_option linter.unusedSectionVars false

theorem i271ONLow_holds : I271ONLow := by
  intro X _ _ hXK K B hH hNorm hON h27
  obtain ⟨hBN, h9⟩ := hNorm
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hBel : IsElemAbelian 3 B := hH.scp.2.1
  have h4 := hH.rank_four
  have hOKof : GLAPPrimeCoreOf 3 K = ⊥ := i271h_primeCoreOf_eq_bot hH.core hH.comp
  have hOK : GLAPPrimeCore 3 ↥K = ⊥ := i271h_primeCore_eq_bot hH.core hH.comp
  obtain ⟨r, hr⟩ := exists_pow_autOrderIn hp hBel hBN
  have hr2 : 2 ≤ r := (Nat.pow_le_pow_iff_right (by norm_num)).1 (hr ▸ h9)
  have hr3 : r ≤ 3 := (Nat.pow_le_pow_iff_right (by norm_num)).1 (hr ▸ h27)
  have hcomp : CFSG.Open.IsComponentOf K ⊤ := i116pI_isComponentOf hH.core hH.comp
  by_cases hr2' : r = 2
  ·
    subst hr2'
    left
    refine ⟨h4, i271h_isInGOne_of_le hBN ?_⟩
    have hHat : LocalBalance.IsHatON (↥K ⧸ GLAPPrimeCore 3 ↥K) := by
      let e : ↥K ≃* (↥K ⧸ GLAPPrimeCore 3 ↥K) :=
        (QuotientGroup.quotientBot (G := ↥K)).symm.trans
          (QuotientGroup.quotientMulEquivOfEq hOK.symm)
      exact i112f_hat_of_mulEquiv e hON
    have hrel : (dQ K).relIndex B ≤ 9 := by
      rw [i271h_dQ_eq_centralizer hOKof, ← i271h_autOrderIn_eq_relIndex hBN, hr]
      norm_num
    have hin := (input23_25_2_of_facts inputOutON_of_hatON inputSylowON_holds_of_hatON
      input23_25_2Facts_holds) X ⊤ K B hH.comp hHat hH.scp hBN hrel
    rw [hOKof, sup_bot_eq] at hin
    refine hin.trans ?_
    unfold gammaLBelow
    refine iSup₂_le fun E hE => ?_
    have hE3 : 3 ≤ CFSG.Open.pRank 3 E := by
      have := hE.2
      rw [i271h_pRank_coe, i271h_pRank_coe] at this
      omega
    exact i271h_le_coreIn_of_le_centralizer hE.1 hE3 (sSup_le fun _ hL => hL.1)
  · have hr3' : r = 3 := by omega
    subst hr3'
    by_cases h5 : 5 ≤ CFSG.Open.pRank 3 B
    ·
      left
      obtain ⟨B₁, hB₁B, hdisj, hcard⟩ := i271h_exists_faithful_complement hBel hBN hr
      refine ⟨h4, i271h_isInGOne_of_generation hBel hBN hr hB₁B hdisj h5 ?_⟩
      have hE : IsElemAbelian 3 B₁ := i271_isElemAbelian_of_le hBel hB₁B
      have hfaith : ∀ e ∈ B₁, (∀ k ∈ K, e * k = k * e) → e = 1 := by
        intro e he hc
        have : e ∈ B₁ ⊓ (B ⊓ Subgroup.centralizer (K : Set X)) :=
          ⟨he, hB₁B he, Subgroup.mem_centralizer_iff.2 fun k hk => (hc k hk).symm⟩
        rw [hdisj] at this
        exact Subgroup.mem_bot.1 this
      have hgen := i2326o_sc_ON onGeneration_holds onOuterTwo_holds hcomp hON.2.2 hE hcard
        (hB₁B.trans hBN) hfaith
      refine hgen.trans (iSup_le fun e => iSup_le fun he => iSup_le fun hne => ?_)
      exact le_iSup_of_le e (le_iSup_of_le he (le_iSup_of_le hne
        (sSup_le fun _ hL => hL.1)))
    · right
      exact ⟨hON, by omega, hr ▸ by norm_num⟩

end ONLow

end CFSG.HardMathSupport.Solomon.Coordinator
