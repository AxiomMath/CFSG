module

import all Certificates.Data.Census
public import Certificates.Data.Kernel.GilmanCensus.Twin

public section

namespace Certificates.GilmanCensusK

open Certificates.Census

@[expose] def pc (m : Nat) : Nat := (List.range 128).countP (fun i => m.testBit i)

theorem countP_or {α : Type} (p q r : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, ¬(p x = true ∧ q x = true)) → (∀ x, r x = (p x || q x)) →
      l.countP r = l.countP p + l.countP q
  | [], _, _ => rfl
  | x :: l, h1, h2 => by
    simp only [List.countP_cons]
    rw [countP_or p q r l (fun y hy => h1 y (by simp [hy])) h2, h2 x]
    have := h1 x (by simp)
    cases hp : p x <;> cases hq : q x <;> simp_all <;> omega

end Certificates.GilmanCensusK

end
