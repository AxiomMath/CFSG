module

public import CFSG.RankThree.PartTwo.Sec4.Item47Native
public import CFSG.RankThree.PartOne.SPOR.OuterSimple
public import CFSG.RankThree.PartOne.KP.Co3Aut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueOuterTwoPartSporadicCases
public import CFSG.Sporadic.FischerOddCore.Fi23Aut
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall2
public import CFSG.Sporadic.ONOddCore.OuterOrder
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

theorem card_outer_le_two_of_center_bot {G : Type*} [Group G] [Finite G]
    (hz : Subgroup.center G = ⊥) (h : Nat.card (MulAut G) ≤ 2 * Nat.card G) :
    Nat.card (Outer G) ≤ 2 := by
  have hinj : Function.Injective (MulAut.conj : G →* MulAut G) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply le_antisymm _ bot_le
    intro g hg
    have hc : g ∈ Subgroup.center G := by
      apply Subgroup.mem_center_iff.mpr
      intro k
      have hk := congrArg (fun a : MulAut G => a k) hg
      change g * k * g⁻¹ = k at hk
      have heq := congrArg (fun a : G => a * g) hk
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using heq.symm
    rwa [hz] at hc
  have hinner : Nat.card (inner G) = Nat.card G := by
    change Nat.card (MulAut.conj : G →* MulAut G).range = Nat.card G
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hq := (inner G).card_eq_card_quotient_mul_card_subgroup
  rw [hinner] at hq
  change Nat.card (MulAut G) = Nat.card (MulAut G ⧸ inner G) * Nat.card G at hq
  change Nat.card (MulAut G ⧸ inner G) ≤ 2
  have hG : 0 < Nat.card G := Nat.card_pos
  nlinarith

section Spor


theorem not_three_dvd_card_outer_sporadic {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hnab : ∃ a b : T, a * b ≠ b * a) {s : TauCeti.SporadicName}
    (e : T ≃* NativeSporadic.Carrier s) : ¬ 3 ∣ Nat.card (Outer T) := by
  have : Finite (MulAut T) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut T))
  have hpos : 0 < Nat.card (Outer T) := Nat.card_pos
  by_cases h7 : s = .Co1 ∨ s = .Co2 ∨ s = .HN ∨ s = .Ly ∨ s = .Th ∨ s = .B ∨ s = .M
  · have h2 := CFSG.RankThree.PartOne.SPOR.sporadicOuterOrderLeTwoSimple_holds s h7 T hnab ⟨e⟩
    omega
  · have hfin : Finite (NativeSporadic.Carrier s) := Finite.of_equiv T e.toEquiv
    have hcard : Nat.card (Outer T) = Nat.card (Outer (NativeSporadic.Carrier s)) :=
      Nat.card_congr (equivalence e).toEquiv
    rw [hcard] at hpos ⊢
    have hmain : Nat.card (Outer (NativeSporadic.Carrier s)) ≤ 2 ∨
        Nat.card (Outer (NativeSporadic.Carrier s)) ∣ 4 := by
      cases s
      · exact Or.inl (CFSG.RankThree.PartTwo.Sec4.card_outer_carrier_le_two (by simp))
      · exact Or.inl (CFSG.RankThree.PartTwo.Sec4.card_outer_carrier_le_two (by simp))
      · exact Or.inl (card_outer_le_two_of_center_bot
          (CFSG.RankThree.PartTwo.Sec4.center_carrier_M22_M24 (Or.inl rfl))
          (CFSG.RankThree.PartTwo.Sec4.card_mulAut_carrier_le_two_mul (Or.inl rfl)))
      · exact Or.inl (CFSG.RankThree.PartTwo.Sec4.card_outer_carrier_le_two (by simp))
      · exact Or.inl (card_outer_le_two_of_center_bot
          (CFSG.RankThree.PartTwo.Sec4.center_carrier_M22_M24 (Or.inr rfl))
          (CFSG.RankThree.PartTwo.Sec4.card_mulAut_carrier_le_two_mul (Or.inr rfl)))
      · exact Or.inl (CFSG.RankThree.PartTwo.Sec4.card_outer_carrier_le_two (by simp))
      · exact Or.inl (CFSG.RankThree.PartTwo.Sec4.card_outer_carrier_le_two (by simp))
      · exact Or.inl (CFSG.RankThree.PartTwo.Sec4.card_outer_carrier_le_two (by simp))
      · exact Or.inl (CFSG.AGLEmbedding.card_outer_J4.le.trans (by norm_num))
      · exact Or.inl (CFSG.RankThree.PartTwo.Sec4.card_outer_carrier_le_two (by simp))
      · exact Or.inl (CFSG.RankThree.PartTwo.Sec4.card_outer_carrier_le_two (by simp))
      · exact Or.inl (CFSG.RankThree.PartTwo.Sec4.card_outer_carrier_le_two (by simp))
      · exact Or.inl (CFSG.RankThree.PartTwo.Sec4.card_outer_carrier_le_two (by simp))
      · exact Or.inl (CFSG.Sporadic.SuzOddCore.outer_carrier_suz.1.le)
      · exact Or.inr CFSG.Sporadic.ONOddCore.r3e_on_outer_order_divides_four.1
      · exact absurd (by simp) h7
      · exact absurd (by simp) h7
      · exact Or.inl (CFSG.RankThree.PartOne.CTUC_Co3_all_automorphisms_inner.{0}.2.2.2.1.le.trans
          (by norm_num))
      · exact Or.inl (CFSG.ComponentClassification.CatalogueOuterTwoPart.card_outer_fi22.le)
      · exact Or.inl (CFSG.Sporadic.FischerOddCore.card_outer_fi23.le.trans (by norm_num))
      · exact Or.inl (CFSG.Sporadic.Schreier.Fi24.card_outer_fi24prime.le)
      · exact absurd (by simp) h7
      · exact absurd (by simp) h7
      · exact absurd (by simp) h7
      · exact absurd (by simp) h7
      · exact absurd (by simp) h7
    rcases hmain with h | h
    · omega
    · intro h3
      have h34 : 3 ∣ 4 := h3.trans h
      omega

end Spor

section Tits


theorem not_three_dvd_card_outer_tits {X : Type} [Group X] {p f : ℕ}
    (h : ReeTitsModel X .Tits p f) : ¬ 3 ∣ Nat.card (Outer X) := by
  obtain ⟨-, -, -, rfl, -⟩ := h.1
  rw [CFSG.RankThree.PartTwo.Sec4.card_outer_tits X f h]
  decide

end Tits

end CFSG.HardMathSupport.Dickson.Sec6.I923
