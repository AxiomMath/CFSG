module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiDefs
public import CFSG.Sporadic.Fi22.Simple
public import CFSG.Sporadic.Fi24.Simple

public section

namespace CFSG.EvenSporadicStandard.Induction

open CFSG.Blueprint.NativeSporadic

theorem noBiggerFi_fi24Prime
    (H : Type) [Group H] : NoBiggerFi H .Fi24Prime := by
  intro L₁ s₁ _ hs₁ _
  have h22 : Nat.card (Carrier .Fi22) = 64561751654400 := CFSG.Sporadic.Fi22.card_Fi22
  have h23 : Nat.card (Carrier .Fi23) = 4089470473293004800 := CFSG.Sporadic.Fi23.card_Fi23
  have hs' : s₁ = .Fi22 ∨ s₁ = .Fi23 ∨ s₁ = .Fi24Prime := by simpa [fiTypes] using hs₁
  have h24' : 4089470473293004800 ≤ Nat.card (Carrier .Fi24Prime) := by
    have := CFSG.Sporadic.Fi24.card_Fi24prime
    show 4089470473293004800 ≤ Nat.card CFSG.Blueprint.NativeSporadic.Fi24prime
    rw [this]
    norm_num
  rcases hs' with rfl | rfl | rfl
  · rw [h22]
    omega
  · rw [h23]
    exact h24'
  · exact le_rfl

end CFSG.EvenSporadicStandard.Induction
