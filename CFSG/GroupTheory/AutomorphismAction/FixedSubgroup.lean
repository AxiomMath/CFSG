module

public import Mathlib.Algebra.Group.Commute.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Map

public section

namespace CFSG.GroupTheory.AutomorphismAction

theorem map_fixedSubgroup_eq {P : Type*} [Group P] (A : Subgroup (MulAut P))
    (Q : Subgroup P) (hQ : ∀ x, x ∈ Q ↔ ∀ a : A, a.val x = x) (φ : MulAut P)
    (hcomm : ∀ a : A, Commute φ a.val) :
    Q.map φ.toMonoidHom = Q := by
  have key : ∀ (ψ : MulAut P), (∀ a : A, Commute ψ a.val) → ∀ x ∈ Q, ψ x ∈ Q := by
    intro ψ hψ x hx
    rw [hQ] at hx ⊢
    intro a
    have := congrArg (fun f : MulAut P => f x) (hψ a).eq
    simp only [MulAut.mul_apply] at this
    rw [← this, hx a]
  have hinv : ∀ a : A, Commute φ⁻¹ a.val := fun a => Commute.inv_left (hcomm a)
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact key φ hcomm y hy
  · intro x hx
    refine ⟨φ⁻¹ x, key φ⁻¹ hinv x hx, ?_⟩
    simp

end CFSG.GroupTheory.AutomorphismAction
