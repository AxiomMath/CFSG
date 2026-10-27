module

public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.HardMathSupport.U4FF

theorem alternating_skew_symm {F : Type} [Field F] {X : Type} [AddCommGroup X] [Module F X]
    {β : LinearMap.BilinForm F X} (h : ∀ x, β x x = 0) (x y : X) :
    β y x = -β x y := by
  have hxy := h (x + y)
  simp only [map_add, LinearMap.add_apply] at hxy
  linear_combination hxy - h x - h y

theorem card_pairs_lt_le_three (r : ℕ) (hr : r ≤ 3) :
    Nat.card {p : Fin r × Fin r // p.1 < p.2} = r * (r - 1) / 2 := by
  interval_cases r <;> rw [Nat.card_eq_fintype_card] <;> decide

theorem card_alternating_le {F : Type} [Field F] [Finite F] {X : Type} [AddCommGroup X]
    [Module F X] [FiniteDimensional F X] (hr : Module.finrank F X ≤ 3) :
    Nat.card {β : LinearMap.BilinForm F X // ∀ x, β x x = 0} ≤
      Nat.card F ^ (Module.finrank F X * (Module.finrank F X - 1) / 2) := by
  let e : Module.Basis (Fin (Module.finrank F X)) F X := Module.finBasis F X
  let φ : {β : LinearMap.BilinForm F X // ∀ x, β x x = 0} →
      ({p : Fin (Module.finrank F X) × Fin (Module.finrank F X) // p.1 < p.2} → F) :=
    fun β p => β.1 (e p.1.1) (e p.1.2)
  have hinj : Function.Injective φ := by
    intro β γ hβγ
    apply Subtype.ext
    apply LinearMap.BilinForm.ext_basis e
    intro i j
    rcases lt_trichotomy i j with hij | hij | hji
    · exact congrFun hβγ ⟨(i, j), hij⟩
    · rw [hij, β.2 (e j), γ.2 (e j)]
    · have h1 : β.1 (e j) (e i) = γ.1 (e j) (e i) := congrFun hβγ ⟨(j, i), hji⟩
      rw [alternating_skew_symm β.2 (e j) (e i), alternating_skew_symm γ.2 (e j) (e i), h1]
  calc Nat.card {β : LinearMap.BilinForm F X // ∀ x, β x x = 0}
      ≤ Nat.card ({p : Fin (Module.finrank F X) × Fin (Module.finrank F X) // p.1 < p.2} → F) :=
        Nat.card_le_card_of_injective φ hinj
    _ = Nat.card F ^
          Nat.card {p : Fin (Module.finrank F X) × Fin (Module.finrank F X) // p.1 < p.2} :=
        Nat.card_fun
    _ = Nat.card F ^ (Module.finrank F X * (Module.finrank F X - 1) / 2) := by
        rw [card_pairs_lt_le_three _ hr]

end CFSG.HardMathSupport.U4FF
