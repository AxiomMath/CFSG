module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi22Core
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiTwoSylowFinkelstein
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Transfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi22Local

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Cover CFSG.EvenSporadicStandard.Solomon78 CFSG.Blueprint.NativeSporadic


theorem solomonCoreP_fi22 (h25 : Finkelstein77.Asc76Lemma25)
    (hr : ∀ (X : Type) [Group X], IsLS [.Fi22] X → 3 ≤ CFSG.pRank 2 X) :
    SolomonCoreP .Fi22 fiIn22 := by
  intro H _ _ N L K t u hcov hhyp hQ
  obtain ⟨huL, hbar, hmodel⟩ := fiIn22_data hcov hQ.1
  obtain ⟨-, hu2, hKL, hKu, hKq, -, -⟩ := hQ.1
  have S := Closing.ClosingSetup.of_hypQ hhyp huL
  have hY : IsSporadic (↥L ⧸ center ↥L) .Fi22 := hcov.2.2
  have hS2 := card_sylow_eq_two_of_finkelstein_of_lemma25_of_pRank h25 hhyp.fstar
    hhyp.index_le_two hhyp.standardL hhyp.quasisimpleL hhyp.centre_odd hhyp.cyclicSylow
    (CFSG.EvenSporadicStandard.HypOne.Fi22.hypothesisOne_of_isSporadic hY)
    (hr _ (isLS_iff.2 ⟨_, List.mem_singleton_self _, hcov⟩)) hhyp.t_mem hhyp.t_order
  have hU : twoAdic (L ⊓ centralizer ({u} : Set H)) < twoAdic L := by
    rw [twoAdic_inf_centralizer_of_cover hcov.odd_center huL hu2 hKL hKu hbar]
    exact twoAdic_lt_of_cover hcov.odd_center huL hKL hmodel hbar
  exact S.false_of_transfer (fi22_autCenterCond2_of_isSporadic hY) (fi22_outTwo_of_isSporadic hY)
    (fi22AutOddCore hY) hS2 hU (hQ.2 N t hhyp)

theorem sol78Closing_fi22 (h25 : Finkelstein77.Asc76Lemma25)
    (hr : ∀ (X : Type) [Group X], IsLS [.Fi22] X → 3 ≤ CFSG.pRank 2 X) :
    Sol78Closing [.Fi22] (fun _ => fiIn22) :=
  sol78Closing_of_partsP (S := [.Fi22]) (Q := fun _ => fiIn22) (P := fun _ => fiIn22)
    (fun s hs => by rcases List.mem_singleton.1 hs with rfl; exact sol78SettingLocalQ_fi22)
    (fun s hs => by rcases List.mem_singleton.1 hs with rfl; exact sol78Local39Q_fi22)
    (fun s hs => by rcases List.mem_singleton.1 hs with rfl; exact solomonCoreP_fi22 h25 hr)

@[expose] def Fi22FixesElem : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (L K : Subgroup H) (u : H), OddCover .Fi22 L →
    fiLoc 18393661440 H L K u → InvolutionFixesElem ↥K 16

theorem lemma36DataQ_fi22 (hfix : Fi22FixesElem) :
    Lemma36DataQ .Fi22 (fiLoc 18393661440) 2 16 := by
  refine ⟨by norm_num, ?_⟩
  intro H _ _ L K u hcov hQ
  obtain ⟨huL, hbar, hmodel⟩ := fiLoc22_data hcov hQ
  obtain ⟨-, hu2, hKL, hKu, hKq, -⟩ := id hQ
  have hC : Nat.card (autCentralizer L K) ≤ 4 :=
    card_autCentralizer_le_of_cover hcov.1.1 hmodel.outTwo
      (by rw [hbar]; exact hmodel.card_centralizer)
  exact ⟨hu2, mem_of_cover hcov.odd_center huL hu2 hbar,
    fun k hk => ⟨hKL hk, mem_centralizer_singleton_iff.2 (hKu k hk)⟩,
    characteristic_of_cover hcov.odd_center hKq huL hu2 hKL hKu hbar, hKq,
    isSolvable_autCentralizer_of_card_le hC, twoAdic_le_two_of_card_le_four _ hC,
    hfix H L K u hcov hQ⟩

end CFSG.EvenSporadicStandard.Induction
