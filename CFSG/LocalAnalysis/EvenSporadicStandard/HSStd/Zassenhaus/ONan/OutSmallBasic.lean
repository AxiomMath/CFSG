module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan

open CFSG.ComponentClassification.OuterAutomorphisms

theorem card_mulAut_le_mul_card_outer (G : Type*) [Group G] [Finite G] :
    Nat.card (MulAut G) ≤ Nat.card (Outer G) * Nat.card G := by
  rw [(inner G).card_eq_card_quotient_mul_card_subgroup]
  exact Nat.mul_le_mul le_rfl (Nat.card_le_card_of_surjective _
    (MonoidHom.rangeRestrict_surjective (MulAut.conj : G →* MulAut G)))

theorem card_mulAut_le_of_card_outer_le {G : Type*} [Group G] [Finite G] {k : ℕ}
    (hout : Nat.card (Outer G) ≤ k) : Nat.card (MulAut G) ≤ k * Nat.card G :=
  (card_mulAut_le_mul_card_outer G).trans (Nat.mul_le_mul_right _ hout)

theorem card_mulAut_le_of_mulEquiv {G H : Type*} [Group G] [Group H] {k : ℕ} (e : G ≃* H)
    (h : Nat.card (MulAut H) ≤ k * Nat.card H) : Nat.card (MulAut G) ≤ k * Nat.card G := by
  rw [Nat.card_congr (MulAut.congr e).toEquiv, Nat.card_congr e.toEquiv]
  exact h

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan
