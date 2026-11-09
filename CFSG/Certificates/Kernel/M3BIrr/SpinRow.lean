module

public import CFSG.Certificates.Kernel.M3BIrr.Mats

public section

namespace CFSG.KD.M3BI

open Timmesfeld.M3B CFSG.HardMathSupport.MathTwE6.M3BIrr CFSG.KC.M3BIrr

@[expose] def spinRow (A B : Mat) (i : Nat) (a₀ a₁ : F3) : Bool :=
  (List.finRange 3).all fun a₂ =>
    (a₀ == 0 && a₁ == 0 && a₂ == 0) || spinFull A B (vmul (vec3 a₀ a₁ a₂) (matBi i))

theorem spinAt_of_rows {A B : Mat} {i : Nat} {a₀ : F3} (h0 : spinRow A B i a₀ 0 = true)
    (h1 : spinRow A B i a₀ 1 = true) (h2 : spinRow A B i a₀ 2 = true) : spinAt A B i a₀ = true := by
  show (List.finRange 3).all (spinRow A B i a₀) = true
  rw [List.all_eq_true]
  intro a₁ _
  match a₁ with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1
  | ⟨2, _⟩ => exact h2

end CFSG.KD.M3BI

end
