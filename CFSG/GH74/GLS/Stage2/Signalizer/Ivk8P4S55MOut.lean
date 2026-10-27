module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open CFSG.ComponentClassification.OuterAutomorphisms

theorem mulAut_card_le_of_outer {G H : Type*} [Group G] [Group H] [Finite G] {k : ℕ}
    (hout : Nat.card (Outer G) ≤ k) (f : G ≃* H) : Nat.card (MulAut H) ≤ k * Nat.card G := by
  rw [← Nat.card_congr (MulAut.congr f).toEquiv,
    (inner G).card_eq_card_quotient_mul_card_subgroup]
  have hinn : Nat.card (inner G) ≤ Nat.card G :=
    Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  exact Nat.mul_le_mul hout hinn

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
