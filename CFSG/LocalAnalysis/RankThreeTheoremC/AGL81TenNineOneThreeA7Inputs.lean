module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fin.VecNotation

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenNineOneThree.A7Ai

open Equiv

@[expose] def c1 : Perm (Fin 7) :=
  ⟨![1, 2, 0, 3, 4, 5, 6], ![2, 0, 1, 3, 4, 5, 6], by decide, by decide⟩

@[expose] def c2 : Perm (Fin 7) :=
  ⟨![0, 1, 2, 4, 5, 3, 6], ![0, 1, 2, 5, 3, 4, 6], by decide, by decide⟩

@[expose] def tab (p : Perm (Fin 7)) : Perm (Fin 7) :=
  let v := Array.ofFn p
  let w := Array.ofFn p.symm
  { toFun := fun i => v[i.1]'(by simp [v])
    invFun := fun i => w[i.1]'(by simp [w])
    left_inv := fun i => by simp [v, w]
    right_inv := fun i => by simp [v, w] }

theorem tab_eq (p : Perm (Fin 7)) : tab p = p := by
  ext i
  simp [tab]

@[expose] def e9 : List (Perm (Fin 7)) :=
  (List.range 3).flatMap fun i => (List.range 3).map fun j => tab (c1 ^ i * c2 ^ j)

@[expose] def vInv : List (Perm (Fin 7)) :=
  [swap 0 1 * swap 2 6, swap 0 2 * swap 1 6, swap 0 6 * swap 1 2,
    swap 3 4 * swap 5 6, swap 3 5 * swap 4 6, swap 3 6 * swap 4 5]

@[expose] def badG (g : Perm (Fin 7)) : Bool :=
  (decide (g * c1 * g⁻¹ ∈ e9) && !decide (g * c1 * g⁻¹ ∈ [1, c1, c1 ^ 2])) ||
    (decide (g * c2 * g⁻¹ ∈ e9) && !decide (g * c2 * g⁻¹ ∈ [1, c2, c2 ^ 2]))

@[expose] def a7aiCheck : Bool :=
  decide (∀ t : Perm (Fin 7), tab t * tab t = 1 → tab t ≠ 1 →
      (∀ x ∈ e9, ∀ y ∈ e9, tab (x * tab t * x⁻¹ * (y * tab t * y⁻¹)) ^ 16 = 1) → tab t ∈ vInv) &&
    decide (∀ g : Perm (Fin 7), badG (tab g) = true → ∀ t ∈ vInv,
      tab (tab g * t * (tab g)⁻¹) ∈ vInv → tab (t * tab (tab g * t * (tab g)⁻¹)) ^ 16 ≠ 1)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenNineOneThree.A7Ai
