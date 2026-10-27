module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.ArithSpor
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.ArithResidual
public import CFSG.Blueprint.EvenStandardExact
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.EvenSporadicStandard.Induction.Thm54Reach

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.GSThmB.QPUSpor (sporOrder)

private theorem card_g2_four (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : LieModel X .G2 0 2 2) : Nat.card X = 251596800 := by
  obtain ⟨-, h1, -⟩ := hO X .G2 0 2 2 h.admissible h
  have hd : lieOrderDivisor .G2 0 (2 ^ 2) = 1 := by decide +kernel
  have hn : lieOrderNumerator .G2 0 (2 ^ 2) = 251596800 := by decide +kernel
  rw [hd, hn] at h1
  simpa using h1

private theorem card_f4_two (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : LieModel X .F4 0 2 1) : Nat.card X = 3311126603366400 := by
  obtain ⟨-, h1, -⟩ := hO X .F4 0 2 1 h.admissible h
  have hd : lieOrderDivisor .F4 0 (2 ^ 1) = 1 := by decide +kernel
  have hn : lieOrderNumerator .F4 0 (2 ^ 1) = 3311126603366400 := by decide +kernel
  rw [hd, hn] at h1
  simpa using h1

private theorem card_twistedE6_two (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : LieModel X .twistedE6 0 2 1) : Nat.card X = 76532479683774853939200 := by
  obtain ⟨-, h1, -⟩ := hO X .twistedE6 0 2 1 h.admissible h
  have hd : lieOrderDivisor .twistedE6 0 (2 ^ 1) = 3 := by decide +kernel
  have hn : lieOrderNumerator .twistedE6 0 (2 ^ 1) = 229597439051324561817600 := by
    decide +kernel
  rw [hd, hn] at h1
  omega

private theorem card_psp_three_two (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : LieModel X .PSp 3 2 1) : Nat.card X = 1451520 := by
  obtain ⟨-, h1, -⟩ := hO X .PSp 3 2 1 h.admissible h
  have hd : lieOrderDivisor .PSp 3 (2 ^ 1) = 1 := by decide +kernel
  have hn : lieOrderNumerator .PSp 3 (2 ^ 1) = 1451520 := by decide +kernel
  rw [hd, hn] at h1
  simpa using h1

private theorem card_psu_six_two (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : LieModel X .PSU 6 2 1) : Nat.card X = 9196830720 := by
  obtain ⟨-, h1, -⟩ := hO X .PSU 6 2 1 h.admissible h
  have hd : lieOrderDivisor .PSU 6 (2 ^ 1) = 3 := by decide +kernel
  have hn : lieOrderNumerator .PSU 6 (2 ^ 1) = 27590492160 := by decide +kernel
  rw [hd, hn] at h1
  omega

private theorem card_pomegaPlus_eight_two (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : LieModel X .POmegaPlus 4 2 1) : Nat.card X = 174182400 := by
  obtain ⟨-, h1, -⟩ := hO X .POmegaPlus 4 2 1 h.admissible h
  have hd : lieOrderDivisor .POmegaPlus 4 (2 ^ 1) = 1 := by decide +kernel
  have hn : lieOrderNumerator .POmegaPlus 4 (2 ^ 1) = 174182400 := by decide +kernel
  rw [hd, hn] at h1
  simpa using h1

private theorem card_pomegaMinus_eight_two (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : LieModel X .POmegaMinus 4 2 1) : Nat.card X = 197406720 := by
  obtain ⟨-, h1, -⟩ := hO X .POmegaMinus 4 2 1 h.admissible h
  have hd : lieOrderDivisor .POmegaMinus 4 (2 ^ 1) = 1 := by decide +kernel
  have hn : lieOrderNumerator .POmegaMinus 4 (2 ^ 1) = 197406720 := by decide +kernel
  rw [hd, hn] at h1
  simpa using h1

theorem not_evenStandardResidual_of_thm54Order (hO : LieOrderFormulasInput)
    (hcard : ∀ s : TauCeti.SporadicName, Nat.card (Carrier s) = sporOrder s)
    {L : Type} [Group L] (hc : Thm54Order (Nat.card (L ⧸ Subgroup.center L))) :
    ¬ Recognition.Exact.EvenStandardResidual L := by
  intro h
  unfold Recognition.Exact.EvenStandardResidual at h
  obtain ⟨-, hA | hB | hC | hD⟩ := h
  ·
    unfold Recognition.Exact.ResidualA CFSG.Blueprint.NativeSporadic.SporadicRep at hA
    obtain ⟨⟨s, ⟨e⟩⟩, -⟩ := hA
    exact Thm54Order.ne_sporOrder hc s ((Nat.card_congr e.toEquiv).trans (hcard s))
  ·
    unfold Recognition.Exact.ResidualB at hB
    obtain ⟨-, hG2 | hF4 | hE6⟩ := hB
    · exact (Thm54Order.ne_residual hc).1 (card_g2_four hO hG2)
    · exact (Thm54Order.ne_residual hc).2.1 (card_f4_two hO hF4)
    · exact (Thm54Order.ne_residual hc).2.2.1 (card_twistedE6_two hO hE6)
  ·
    unfold Recognition.Exact.ResidualC at hC
    rcases hC with hSp6 | hU6 | hO8
    · exact (Thm54Order.ne_residual hc).2.2.2.1 (card_psp_three_two hO hSp6)
    · exact (Thm54Order.ne_residual hc).2.2.2.2.1 (card_psu_six_two hO hU6)
    · exact (Thm54Order.ne_residual hc).2.2.2.2.2.1 (card_pomegaPlus_eight_two hO hO8)
  ·
    unfold Recognition.Exact.ResidualD at hD
    obtain ⟨hz, hL⟩ := hD
    have hq : Nat.card (L ⧸ Subgroup.center L) = Nat.card L := by
      rw [hz]
      exact Nat.card_congr QuotientGroup.quotientBot.toEquiv
    exact (Thm54Order.ne_residual hc).2.2.2.2.2.2
      (hq.trans (card_pomegaMinus_eight_two hO hL))

end CFSG.EvenSporadicStandard.Induction.Thm54Reach
