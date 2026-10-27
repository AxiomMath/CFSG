module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

@[expose] def inn (Y : Type*) [Group Y] : Subgroup (MulAut Y) :=
  (MulAut.conj : Y →* MulAut Y).range

theorem mem_inn {Y : Type*} [Group Y] {α : MulAut Y} : α ∈ inn Y ↔ ∃ x : Y, MulAut.conj x = α :=
  Iff.rfl

@[expose] def OutPTwoGen (Y : Type*) [Group Y] (p : ℕ) : Prop :=
  ∀ P : Subgroup (MulAut Y), IsPGroup p P → ∃ a ∈ P, ∃ b ∈ P, P ≤ Subgroup.closure {a, b} ⊔ inn Y

@[expose] def OutPInner (Y : Type*) [Group Y] (p : ℕ) : Prop :=
  ∀ P : Subgroup (MulAut Y), IsPGroup p P → P ≤ inn Y

theorem OutPInner.outPTwoGen {Y : Type*} [Group Y] {p : ℕ} (h : OutPInner Y p) :
    OutPTwoGen Y p := fun P hP =>
  ⟨1, P.one_mem, 1, P.one_mem, (h P hP).trans le_sup_right⟩

@[expose] def AutScalarTorus (Y : Type*) [Group Y] : Prop :=
  ∀ (S₀ : Sylow 2 Y) (α : MulAut Y), (S₀ : Subgroup Y).map α.toMonoidHom = S₀ →
    (∃ e : ℕ, 0 < e ∧ Nat.Coprime e 6 ∧ α ^ e ∈ inn Y) →
      ∃ k : ℕ, ∀ b ∈ Subgroup.normalizer ((S₀ : Subgroup Y) : Set Y),
        α b * (b ^ k)⁻¹ ∈ (S₀ : Subgroup Y)

end CFSG.AGLEmbedding.ParabAutIrr
