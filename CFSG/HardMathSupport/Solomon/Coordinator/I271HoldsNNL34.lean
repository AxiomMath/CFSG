module

public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsNN
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsL34
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KEvenSLTwo

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Equiv Equiv.Perm MulAction CFSG.Open CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  GL83 GL83.CompFam CFSG.HardMathSupport.Solomon.UniquenessMaximal

section Main

variable {X : Type} [Group X] [Finite X]

theorem nnExc_slThreeFour : NNExc (fun _ _ K => IsSLThreeFour ↥K) := by
  intro X _ _ hXK K B hH _ _ h4 _ hSL
  have hBel : IsElemAbelian 3 B := hH.scp.2.1
  set A : Subgroup X := B ⊓ Subgroup.normalizer (K : Set X) with hA
  have hAB : A ≤ B := inf_le_left
  have hAN : A ≤ Subgroup.normalizer (K : Set X) := inf_le_right
  have hAel : IsElemAbelian 3 A := elem_mono hBel hAB
  have hOK : GLAPPrimeCore 3 ↥K = ⊥ := i271h_primeCore_eq_bot hH.core hH.comp
  have hOKof : GLAPPrimeCoreOf 3 K = ⊥ := i271h_primeCoreOf_eq_bot hH.core hH.comp
  have hbar : IsLThreeFour (↥K ⧸ GLAPPrimeCore 3 ↥K) ∨
      IsSLThreeFour (↥K ⧸ GLAPPrimeCore 3 ↥K) := by
    right
    let e : ↥K ≃* (↥K ⧸ GLAPPrimeCore 3 ↥K) :=
      (QuotientGroup.quotientBot (G := ↥K)).symm.trans (QuotientGroup.quotientMulEquivOfEq hOK.symm)
    exact i271h_isSLThreeFour_of_mulEquiv e hSL
  have hmain := input23_20_proved X ⊤ K A hH.comp hbar le_top hAel hAN
  rcases hmain with h | ⟨hinn, hrel⟩
  ·
    left
    have hN1 : 1 ≤ CFSG.Open.pRank 3 A := by
      have hC : B ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥ := hH.centralized
      have hCA : B ⊓ Subgroup.centralizer (K : Set X) ≤ A :=
        inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)
      have hCel : IsElemAbelian 3 (B ⊓ Subgroup.centralizer (K : Set X)) :=
        elem_mono hBel inf_le_left
      obtain ⟨j, hj⟩ := exists_card_eq_pow hCel
      have hj1 : 1 ≤ j := by
        by_contra h0
        have : j = 0 := by omega
        rw [this, pow_zero] at hj
        exact hC (Subgroup.eq_bot_of_card_eq _ hj)
      exact hj1.trans (CFSG.SectionRank.le_pRank Nat.prime_three.one_lt hCA hCel hj)
    have hK' : K ≤ gammaPrimeIn 3 (CFSG.Open.pRank 3 A - 1) A K := by
      rw [hOKof, sup_bot_eq] at h
      refine h.trans ?_
      unfold gammaClBelow
      refine iSup₂_le fun E hE => ?_
      have hE3 : CFSG.Open.pRank 3 A - 1 ≤ CFSG.Open.pRank 3 E := by
        have := hE.2
        rw [i271h_pRank_coe, i271h_pRank_coe] at this
        exact this
      refine sup_le ?_ ?_
      · exact (Subgroup.map_subtype_le _).trans (i224_le_gammaPrimeIn hE.1 hE3)
      · exact (sSup_le fun _ hL => hL.1).trans (i224_le_gammaPrimeIn hE.1 hE3)
    exact nn_caseA_of_hyperplane hH.comp hBel hH.rank_four hN1 hK'
  ·
    right; right
    have hdQ := i271h_dQ_eq_centralizer hOKof
    have hAut9 : autOrderIn B K = 9 := by
      have h : autOrderIn B K = (Subgroup.centralizer (K : Set X)).relIndex A := rfl
      rw [h, ← hdQ]
      exact hrel
    have hInn : InducesInnerIn B K := by
      intro b hb
      obtain ⟨k, hk, hbk⟩ := hinn b hb
      refine ⟨k, hk, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := Subgroup.mem_bot.1 (hOKof ▸ hbk y hy)
      have h2 : b * y * b⁻¹ = k * y * k⁻¹ := by
        rw [mul_inv_eq_one] at h1
        exact h1
      calc y * (k⁻¹ * b) = k⁻¹ * (k * y * k⁻¹) * b := by group
        _ = k⁻¹ * (b * y * b⁻¹) * b := by rw [h2]
        _ = k⁻¹ * b * y := by group
    exact ⟨EvenSL.isLThreeFour_quot_center_of_isSLThreeFour hSL, h4, hAut9, hInn⟩

end Main

end CFSG.HardMathSupport.Solomon.Coordinator
