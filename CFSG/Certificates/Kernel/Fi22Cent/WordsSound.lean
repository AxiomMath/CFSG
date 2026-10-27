module

public import Certificates.Data.Kernel.Fi22Cent.Words
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.Group.End

public section

namespace CFSG.KC.Fi22Cent

theorem wAt_nil {α : Type} (f : α → ℕ → ℕ) (y : ℕ) : wAt f [] y = y := rfl

theorem wAt_cons {α : Type} (f : α → ℕ → ℕ) (l : α) (w : List α) (y : ℕ) :
    wAt f (l :: w) y = f l (wAt f w y) := rfl

theorem wAt_eq {n : ℕ} {α : Type} {g : α → Equiv.Perm (Fin n)} {f : α → ℕ → ℕ}
    (hf : ∀ l (y : Fin n), f l y = ((g l y : Fin n) : ℕ)) (w : List α) (y : Fin n) :
    wAt f w y = (((w.map g).prod y : Fin n) : ℕ) := by
  induction w with
  | nil => rw [wAt_nil, List.map_nil, List.prod_nil, Equiv.Perm.one_apply]
  | cons l w ih => rw [wAt_cons, ih, hf, List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]

end CFSG.KC.Fi22Cent

end
