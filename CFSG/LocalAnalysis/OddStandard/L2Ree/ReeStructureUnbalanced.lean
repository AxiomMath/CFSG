module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSimpleRecognition
public import CFSG.ClassicalInvolution.Orders.Ree
public import CFSG.LocalAnalysis.OddStandard.Children

public section

namespace CFSG.OddStandard.L2Ree

open Subgroup CFSG.Blueprint CFSG.Open

theorem two_thousand_lt_ordRee {f : ℕ} (hf : 3 ≤ f) : 2520 < ordRee (3 ^ f) := by
  have hq : 27 ≤ 3 ^ f :=
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  unfold ordRee
  generalize 3 ^ f = q at hq ⊢
  have h1 : 27 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h2 : 1 ≤ q - 1 := by omega
  have h3 : 1 ≤ q ^ 3 + 1 := by omega
  calc 2520 < 27 ^ 3 := by norm_num
    _ ≤ q ^ 3 := h1
    _ = q ^ 3 * 1 * 1 := by ring
    _ ≤ q ^ 3 * (q ^ 3 + 1) * (q - 1) := Nat.mul_le_mul (Nat.mul_le_mul le_rfl h3) h2

section Ree


theorem two_thousand_lt_card_of_lieModel {Y : Type} [Group Y] {f : ℕ}
    (hm : LieModel Y .twistedG2 0 3 f) : 2520 < Nat.card Y := by
  obtain ⟨-, a, ha, hfa, hcard⟩ :=
    CFSG.ClassicalInvolution.card_of_reeTitsModel_twistedG2
      (LieModel.reeTitsModel hm (by decide)).2
  rw [hcard]
  exact two_thousand_lt_ordRee (by omega)

theorem ree_unbalanced {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hS : StandardSetting G L) {f : ℕ} (hm : LieModel (L ⧸ center L) .twistedG2 0 3 f)
    (hU : CFSG.ComponentClassification.OutcomeLocal.UOutcome G) :
    AltOutcome G ∨ OddLieType G := by
  haveI := hS.simple
  obtain ⟨hout, -⟩ := CFSG.ComponentClassification.CTUSimple.outcome_of_uOutcome hS.nonab hU
  rcases hout with hodd | ⟨n, h7, hn, ⟨e⟩⟩
  · exact .inr hodd
  · refine .inl ⟨n, ?_, ⟨e⟩⟩
    by_contra hlt
    have hn7 : n = 7 := by omega
    subst hn7
    have hbig := two_thousand_lt_card_of_lieModel hm
    have hGcard : Nat.card G = 2520 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    have h1 : Nat.card (L ⧸ center L) ≤ Nat.card L :=
      Nat.card_le_card_of_surjective _ (QuotientGroup.mk_surjective)
    have h2 : Nat.card L ≤ Nat.card G :=
      Nat.card_le_card_of_injective _ Subtype.val_injective
    omega

end Ree

end CFSG.OddStandard.L2Ree
