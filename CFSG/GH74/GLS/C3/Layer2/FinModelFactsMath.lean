module

public import CFSG.GH74.GLS.C3.Layer2.FinModelFactsDataInputs

public section

namespace CFSG.GH74.GLS.C3.Layer2.Model

open Equiv Perm CFSG.GH74.GLS.C3.Layer2

namespace Facts

structure FactsProp (n : ℕ) [NeZero n] : Prop where
  sq : a0perm n * a0perm n = 1
  notin : a0perm n ∉ Rl n
  norm : ∀ p ∈ Rl n, a0perm n * p * (a0perm n)⁻¹ ∈ Rl n
  odd : ∀ p ∈ Rl n, p * a0perm n * (p * a0perm n) = 1 → p * a0perm n ≠ 1 →
    numMoved (p * a0perm n) = 8
  conj : ∀ p ∈ Rl n, p * a0perm n * (p * a0perm n) = 1 →
    ∃ r ∈ Rl n, r * a0perm n * r⁻¹ = p * a0perm n
  nodup : (Sl n).Nodup
  cent : ∀ y ∈ Sl n, y * y = 1 → y ≠ 1 →
    ((Sl n).filter fun p => decide (y * p = p * y)).length = 64 →
      y = emb n (x0 n) ∨ y = a0perm n * emb n (x0 n) * (a0perm n)⁻¹
  eta : ∀ (K : Type) [Group K] (φ ψ : K →* Perm (Fin (n + 4))), Function.Injective φ →
    (∀ p ∈ Cl n, ∃ x, φ x = p) → (∀ x, ψ x ∈ Rl n) → (∀ c, φ c = a0perm n → ψ c = emb n (x0 n)) →
    ∃ w : K, orderOf w = 2 ∧ numMoved (ψ w) ≠ exOf (Rl n) (φ w)

end Facts

end CFSG.GH74.GLS.C3.Layer2.Model

end
