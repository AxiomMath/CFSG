module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData

public section

open CFSG.ComponentClassification.PSL3Four

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

structure KB813Model : Prop where
  e16 : ∃ F : Subgroup (Equiv.Perm (Fin 42)), F ≤ S ∧ Nat.card F = 16 ∧
    (∀ f ∈ F, ∀ g ∈ F, f * g = g * f) ∧ ∀ f ∈ F, f * f = 1
  cent : ∀ x ∈ R, x ≠ 1 → x ^ 3 = 1 → ∃ d ∈ C₁, d * x ≠ x * d
  exp27 : ∀ x ∈ R, x ^ 27 = 1 → x ^ 3 = 1
  fix : ∀ y ∈ R, y ∉ S → y ^ 3 = 1 → r₄ * y = y * r₄ →
    ∃ d ∈ C₄, (y * (d * y * d⁻¹)) ^ 3 ≠ 1

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
