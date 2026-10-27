module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6cAEQ

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

structure AE6Fin : Prop where
  trans : ∀ x y : AEQ 6, InU x → InU y → x ≠ 1 → y ≠ 1 → ∃ g ∈ TL4.aeModel 6, g * x * g⁻¹ = y
  centU : ∀ (α : Finset (Fin 6)) (h : α.card = 4) (b : Bool) (x : AEQ 6), InU x →
    (∀ k ∈ memBar α h b, k * x = x * k) → (∀ k ∈ memBar α h (!b), k * x = x * k) →
      x = 1 ∨ x = zBar α h
  twin2 : ∀ (α : Finset (Fin 6)) (h : α.card = 4) (b : Bool), ∃ f : Fin 8 → AEQ 6, Function.Injective f ∧
    ∀ i, TC.Thin.permQ 6 (f i) = 1 ∧ ∃ k ∈ memBar α h b, ∃ k' ∈ memBar α h (!b), f i = k * k'
  twin3 : ∀ (α : Finset (Fin 6)) (h : α.card = 4) (b : Bool) (x y : AEQ 6),
    (∀ k ∈ memBar α h b, k * x = x * k) → (∀ k ∈ memBar α h (!b), k * x = x * k) →
    (∀ k ∈ memBar α h b, k * y = y * k) → (∀ k ∈ memBar α h (!b), k * y = y * k) →
    x * x = zBar α h → y * y = 1 → y * x * y⁻¹ = x * zBar α h →
      TC.Thin.permQ 6 y = 1 ∨ TC.Thin.permQ 6 (y * x) = 1
  twin4 : ∀ (α : Finset (Fin 6)) (h : α.card = 4) (b : Bool) (g : AEQ 6),
    (∀ x : AEQ 6, InU x → x * g * x⁻¹ * g⁻¹ = 1 ∨ x * g * x⁻¹ * g⁻¹ = zBar α h) →
    (∃ x : AEQ 6, InU x ∧ x * g * x⁻¹ * g⁻¹ = zBar α h) → ∀ δ : AEQ 6, TC.Thin.permQ 6 δ = 1 →
    (∀ k ∈ memBar α h b, k * δ = δ * k) → (∀ k ∈ memBar α h (!b), k * δ = δ * k) →
      δ ≠ 1 → δ ≠ zBar α h → g * δ * g⁻¹ ≠ δ

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c
