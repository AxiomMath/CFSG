module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod

public section

namespace CFSG.ComponentClassification.HarrisLit.EndB

@[expose] def ci (T : ℕ → ℕ → ℕ) (I : ℕ → ℕ) (i j : ℕ) : ℕ := T (T (T i j) (I i)) (I j)

@[expose] def sigProdIdx (T : ℕ → ℕ → ℕ) (o z : ℕ) (a : ℕ × ℕ × ℕ × ℕ)
    (p : (Fin 4 → Bool) × Bool) : ℕ :=
  T (T (T (T (if p.1 0 then a.1 else o) (if p.1 1 then a.2.1 else o))
    (if p.1 2 then a.2.2.1 else o)) (if p.1 3 then a.2.2.2 else o)) (if p.2 then z else o)

@[expose] def quadFun (a : ℕ × ℕ × ℕ × ℕ) : Fin 4 → ℕ := ![a.1, a.2.1, a.2.2.1, a.2.2.2]

@[expose] def sigIdx (T : ℕ → ℕ → ℕ) (I : ℕ → ℕ) (o z : ℕ) (sq : Fin 4 → Bool)
    (cm : Fin 4 → Fin 4 → Bool) (a : ℕ × ℕ × ℕ × ℕ) : Bool :=
  decide ((∀ k, T (quadFun a k) (quadFun a k) = if sq k then z else o) ∧
    (∀ k l, ci T I (quadFun a k) (quadFun a l) = if cm k l then z else o) ∧
    Function.Injective (sigProdIdx T o z a))

@[expose] def quads (L₀ L₁ L₂ L₃ : List ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  L₀ ×ˢ (L₁ ×ˢ (L₂ ×ˢ L₃))

end CFSG.ComponentClassification.HarrisLit.EndB
