module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AR

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.ComponentClassification.CatLeaf
open CFSG.Blueprint.Chevalley
open CFSG.ComponentClassification.GSThmB.QPUSpor (sporOrder)

private lemma sporOrder_ne_target (s : TauCeti.SporadicName) :
    sporOrder s ≠ 262080 ∧ sporOrder s ≠ 5515776 ∧ sporOrder s ≠ 16482816 := by
  cases s <;> decide +kernel

theorem y6f4a_not_exception (hO : LieOrderFormulasInput)
    (hcard : ∀ s : TauCeti.SporadicName, Nat.card (Carrier s) = sporOrder s)
    (hG2 : ∀ (k : Type) [Field k] [Finite k], Nat.card k = 2 →
      Nat.card ↥(⁅adjointGroup .G2 k, adjointGroup .G2 k⁆ : Subgroup (ModGL .G2 k)) = 6048)
    {X : Type} [Group X] (h : Y6TargetLie X) :
    ¬ Recognition.Exact.EvenStandardException X := by
  have hc := y6f4a_card_target hO h
  have hsn := y6f4a_target_simple_nonab hO h
  rintro (h1 | h1 | h1 | ⟨K, hKfld, hKft, hKcard, ⟨e⟩⟩ | ⟨K, hKfld, hKft, hKcard, ⟨e⟩⟩ |
    h1 | h1 | h1)
  · have h60 := y6f4a_card_psl_two_four hO h1
    rcases hc with hc | hc | hc <;> omega
  · have h168 := y6f4a_card_psl_three_two hO h1
    rcases hc with hc | hc | hc <;> omega
  · have h20160 := y6f4a_card_psl_four_two hO h1
    rcases hc with hc | hc | hc <;> omega
  ·
    have hK2 : Nat.card K = 2 := by rw [Nat.card_eq_fintype_card, hKcard]
    have hXc : Nat.card X = Nat.card ↥(commutator (Matrix.symplecticGroup (Fin 2) K)) :=
      Nat.card_congr e.toEquiv
    have hmat : Nat.card (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 65536 := by
      rw [Matrix.card_matrix, hK2]
      norm_num [Nat.card_sum, Nat.card_fin]
    have hle1 : Nat.card ↥(commutator (Matrix.symplecticGroup (Fin 2) K)) ≤
        Nat.card ↥(Matrix.symplecticGroup (Fin 2) K) := Subgroup.card_le_card_group _
    have hle2 : Nat.card ↥(Matrix.symplecticGroup (Fin 2) K) ≤
        Nat.card (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :=
      Nat.card_le_card_of_injective _ Subtype.val_injective
    rcases hc with hc | hc | hc <;> omega
  ·
    have hK2 : Nat.card K = 2 := by rw [Nat.card_eq_fintype_card, hKcard]
    have hX : Nat.card X = 6048 := by
      rw [Nat.card_congr e.toEquiv]
      exact hG2 K hK2
    rcases hc with hc | hc | hc <;> omega
  · have h25920 := y6f4a_card_psu_four_two hO h1
    rcases hc with hc | hc | hc <;> omega
  · have h20160' := y6f4a_card_psl_three_four hO h1
    rcases hc with hc | hc | hc <;> omega
  · obtain ⟨eHe⟩ := h1
    have hX : Nat.card X = 4030387200 := by
      rw [Nat.card_congr eHe.toEquiv, hcard .He]
      decide +kernel
    rcases hc with hc | hc | hc <;> omega

theorem y6f4a_not_residual (hO : LieOrderFormulasInput)
    (hcard : ∀ s : TauCeti.SporadicName, Nat.card (Carrier s) = sporOrder s) {L : Type} [Group L]
    (h : Y6TargetLie (L ⧸ Subgroup.center L)) : ¬ Recognition.Exact.EvenStandardResidual L := by
  intro hres
  unfold Recognition.Exact.EvenStandardResidual at hres
  obtain ⟨-, hA | hB | hC | hD⟩ := hres
  ·
    unfold Recognition.Exact.ResidualA CFSG.Blueprint.NativeSporadic.SporadicRep at hA
    obtain ⟨⟨s, ⟨e⟩⟩, -⟩ := hA
    have hQ : Nat.card (L ⧸ Subgroup.center L) = sporOrder s :=
      (Nat.card_congr e.toEquiv).trans (hcard s)
    obtain ⟨h1, h2, h3⟩ := sporOrder_ne_target s
    rcases y6f4a_card_target hO h with hc | hc | hc
    · exact h1 (hQ.symm.trans hc)
    · exact h2 (hQ.symm.trans hc)
    · exact h3 (hQ.symm.trans hc)
  ·
    unfold Recognition.Exact.ResidualB at hB
    obtain ⟨-, hG2 | hF4 | hE6⟩ := hB
    · have hg := y6f4a_card_g2_four hO hG2
      rcases y6f4a_card_target hO h with hc | hc | hc <;> omega
    · have hg := y6f4a_card_f4_two hO hF4
      rcases y6f4a_card_target hO h with hc | hc | hc <;> omega
    · have hg := y6f4a_card_twistedE6_two hO hE6
      rcases y6f4a_card_target hO h with hc | hc | hc <;> omega
  ·
    unfold Recognition.Exact.ResidualC at hC
    rcases hC with hSp6 | hU6 | hO8
    · have hg := y6f4a_card_psp_three_two hO hSp6
      rcases y6f4a_card_target hO h with hc | hc | hc <;> omega
    · have hg := y6f4a_card_psu_six_two hO hU6
      rcases y6f4a_card_target hO h with hc | hc | hc <;> omega
    · have hg := y6f4a_card_pomegaPlus_eight_two hO hO8
      rcases y6f4a_card_target hO h with hc | hc | hc <;> omega
  ·
    unfold Recognition.Exact.ResidualD at hD
    obtain ⟨hz, hL⟩ := hD
    have hq : Nat.card (L ⧸ Subgroup.center L) = Nat.card L := by
      rw [hz]
      exact Nat.card_congr QuotientGroup.quotientBot.toEquiv
    have hg := y6f4a_card_pomegaMinus_eight_two hO hL
    rcases y6f4a_card_target hO h with hc | hc | hc <;> rw [hq] at hc <;> omega

end CFSG.OddStandard.HigherRank.YamadaG23
