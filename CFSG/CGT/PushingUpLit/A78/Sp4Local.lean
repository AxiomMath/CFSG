module

public import CFSG.Timmesfeld.ARS.Defs

public section

namespace CFSG.CGT.PushingUpLit.A78

open CFSG.Timmesfeld.ARS

variable {G : Type} [Group G]

@[expose] def zClass (Z : Subgroup G) : Set (Subgroup G) := Set.range (conjSub Z)

structure Sp4Local (G : Type) [Group G] (Z : Subgroup G) (e : ℕ) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  two_le : 2 ≤ e
  card : Nat.card Z = 2 ^ e
  sq : ∀ z ∈ Z, z * z = 1
  abelian_le : ∀ E : Subgroup G, (∀ x ∈ E, ∀ y ∈ E, Commute x y) → (∀ x ∈ E, x * x = 1) →
    Nat.card E ≤ 2 ^ (3 * e)
  sigma_trans : ∀ B ∈ sigmaSet (zClass Z) Z, ∀ C ∈ sigmaSet (zClass Z) Z,
    ∀ D ∈ sigmaSet (zClass Z) Z, Commuting B C → Commuting C D → Commuting B D
  sigma_clique : ∀ B ∈ sigmaSet (zClass Z) Z,
    Nat.card {C : Subgroup G // C ∈ sigmaSet (zClass Z) Z ∧ Commuting B C} = 2 ^ e
  sigma_card : Nat.card (sigmaSet (zClass Z) Z) = 2 ^ e * (2 ^ e + 1)
  dual : ∀ C ∈ zClass Z, ¬ Commuting Z C → ∃ I : Subgroup G,
    Nonempty (↥(Z ⊔ C) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)) ∧
    Nonempty (↥I ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)) ∧
    Commuting (Z ⊔ C) I ∧
    (∀ P : Subgroup G, P ≤ I → Nat.card P = 2 ^ e → P ∈ zClass Z) ∧
    (∀ X ∈ zClass Z, Commuting X Z → Commuting X C → X ≤ I) ∧
    (∀ X ∈ zClass Z, Commuting X I → X ≤ Z ⊔ C)

end CFSG.CGT.PushingUpLit.A78
