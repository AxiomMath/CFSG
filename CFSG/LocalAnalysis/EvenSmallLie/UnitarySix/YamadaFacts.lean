module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeParabolic

public section

namespace CFSG.EvenSmallLie.UnitarySix.Yamada

open Subgroup CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def fixedSubgroup {Q : Type*} [Group Q] (α : MulAut Q) : Subgroup Q :=
  α.toMonoidHom.eqLocus (MonoidHom.id Q)

theorem mem_fixedSubgroup {Q : Type*} [Group Q] {α : MulAut Q} {x : Q} :
    x ∈ fixedSubgroup α ↔ α x = x :=
  Iff.rfl

structure YamadaFacts {Q : Type} [Group Q] (D : ToddParabolic Q) : Prop where
  card_outer : Nat.card (Outer Q) = 6
  rank : ∀ α : MulAut Q, α * α = 1 → (∀ m : Q, α ≠ MulAut.conj m) → ∀ B : Subgroup Q,
    (∀ b ∈ B, α b = b) → (∀ b ∈ B, b ^ 2 = 1) → Nat.card B ≤ 2 ^ 6
  fusion : ∀ α : MulAut Q, α * α = 1 → (∀ m : Q, α ≠ MulAut.conj m) → ∃ l : Q,
    l * (α l)⁻¹ ≠ 1 ∧ l * (α l)⁻¹ ∈
      ⁅⁅fixedSubgroup α, fixedSubgroup α⁆, ⁅fixedSubgroup α, fixedSubgroup α⁆⁆
  centralizer_A : ∀ α : MulAut Q, (∀ a ∈ D.A, α a = a) → ∃ a ∈ D.A, α = MulAut.conj a
  comm_a₁ : D.a₁ ∈ ⁅centralizer ({D.a₁} : Set Q), centralizer ({D.a₁} : Set Q)⁆
  comm_a₂ : D.a₂ ∈ ⁅centralizer ({D.a₂} : Set Q), centralizer ({D.a₂} : Set Q)⁆
  two_trans : ∀ x ∈ conjClass D.K D.a₁, ∀ y ∈ conjClass D.K D.a₁, ∀ z ∈ conjClass D.K D.a₁,
    ∀ w ∈ conjClass D.K D.a₁, x ≠ y → z ≠ w → ∃ k ∈ D.K, k * x * k⁻¹ = z ∧ k * y * k⁻¹ = w

end CFSG.EvenSmallLie.UnitarySix.Yamada
