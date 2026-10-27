module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagUa

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OutInv

open CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

@[expose] def fixSub {X : Type*} [Group X] (φ : MulAut X) : Subgroup X where
  carrier := {x | φ x = x}
  mul_mem' := fun {a b} (ha : φ a = a) (hb : φ b = b) => show φ (a * b) = a * b by
    rw [map_mul, ha, hb]
  one_mem' := map_one φ
  inv_mem' := fun {a} (ha : φ a = a) => show φ a⁻¹ = a⁻¹ by
    rw [map_inv, ha]

theorem mem_fixSub {X : Type*} [Group X] {φ : MulAut X} {x : X} : x ∈ fixSub φ ↔ φ x = x :=
  Iff.rfl

@[expose] def OuterInvCentL4 : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    Fintype.card F = p ^ f →
    ∀ φ : MulAut (LinearFlag.projectiveSL 4 F), φ ^ 2 = 1 → φ ∉ (LinearFlag.conjAut 4 F).range →
      ∀ J' : Subgroup (LinearFlag.projectiveSL 4 F), J' ≤ fixSub φ →
        IsComponent (J'.subgroupOf (fixSub φ)) →
        Blueprint.LieModel (↥J' ⧸ center ↥J') .PSL 2 p (2 * f) →
        (∀ ψ : MulAut (LinearFlag.projectiveSL 4 F), ψ * φ = φ * ψ → (∀ x ∈ J', ψ x = x) →
          (∃ k : ℕ, ψ ^ 2 ^ k = 1) → ψ ∈ zpowers φ) ∧
        ∀ ζ ∈ J', orderOf ζ = 2 → ∃ γ : LinearFlag.projectiveSL 4 F,
          (MulAut.conj γ)⁻¹ * φ * MulAut.conj γ = φ * MulAut.conj ζ

@[expose] def OuterInvCentU4 : Prop :=
  ∀ (K : Type) [Field K] (p f : ℕ) (h : UnitaryFieldData p f K), p ≠ 2 →
    ∀ φ : MulAut (StatedProj (StatedSU 4 (p ^ f) K)), φ ^ 2 = 1 → φ ∉ DiagU.InnU p f K h →
      ∀ J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K)), J' ≤ fixSub φ →
        IsComponent (J'.subgroupOf (fixSub φ)) →
        Blueprint.LieModel (↥J' ⧸ center ↥J') .PSL 2 p (2 * f) →
        (∀ ψ : MulAut (StatedProj (StatedSU 4 (p ^ f) K)), ψ * φ = φ * ψ →
          (∀ x ∈ J', ψ x = x) → (∃ k : ℕ, ψ ^ 2 ^ k = 1) → ψ ∈ zpowers φ) ∧
        ∀ ζ ∈ J', orderOf ζ = 2 → ∃ γ : StatedProj (StatedSU 4 (p ^ f) K),
          (MulAut.conj γ)⁻¹ * φ * MulAut.conj γ = φ * MulAut.conj ζ

@[expose] def OuterInvCentO8 : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (p e : ℕ), p.Prime → p ≠ 2 → 1 ≤ e →
    Fintype.card K = p ^ e → ∀ b c : K, (∀ t : K, t ^ 2 + b * t + c ≠ 0) →
    ∀ φ : MulAut (StatedProj (StatedOmega (StatedQuadMinus 4 K b c))), φ ^ 2 = 1 →
      φ ∉ (MulAut.conj : StatedProj (StatedOmega (StatedQuadMinus 4 K b c)) →* _).range →
      ∀ J' : Subgroup (StatedProj (StatedOmega (StatedQuadMinus 4 K b c))), J' ≤ fixSub φ →
        IsComponent (J'.subgroupOf (fixSub φ)) →
        Blueprint.LieModel (↥J' ⧸ center ↥J') .PSL 2 p (2 * (2 * e)) →
        (∀ ψ : MulAut (StatedProj (StatedOmega (StatedQuadMinus 4 K b c))), ψ * φ = φ * ψ →
          (∀ x ∈ J', ψ x = x) → (∃ k : ℕ, ψ ^ 2 ^ k = 1) → ψ ∈ zpowers φ) ∧
        ∀ ζ ∈ J', orderOf ζ = 2 → ∃ γ : StatedProj (StatedOmega (StatedQuadMinus 4 K b c)),
          (MulAut.conj γ)⁻¹ * φ * MulAut.conj γ = φ * MulAut.conj ζ

end OutInv

end CFSG.ComponentClassification.CatFactsL4U4
