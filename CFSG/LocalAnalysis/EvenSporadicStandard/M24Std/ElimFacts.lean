module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup
open scoped MatrixGroups

@[expose] def GoldschmidtClass {G : Type} [Group G] (T C B : Subgroup G) : Prop :=
  B ≤ T ∧ ¬ B ≤ C ∧ ∃ g : G, B.map (MulAut.conj g).toMonoidHom ≤ C

@[expose] def Goldschmidt74Cor4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Sylow 2 G) (C : Subgroup G),
    C ≤ (T : Subgroup G) → (∀ c ∈ C, ∀ c' ∈ C, c * c' = c' * c) → (∀ c ∈ C, c * c = 1) →
    (∀ g : G, C.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      C.map (MulAut.conj g).toMonoidHom = C) →
    (∃ c ∈ C, ∃ g : G, g * c * g⁻¹ ∈ (T : Subgroup G) ∧ g * c * g⁻¹ ∉ C) →
    ∃ ρ : ℕ,
      (∃ B, GoldschmidtClass (T : Subgroup G) C B ∧
        (centralizer (C : Set G)).relIndex B = ρ) ∧
      (∀ B, GoldschmidtClass (T : Subgroup G) C B → (centralizer (C : Set G)).relIndex B ≤ ρ) ∧
      (∃ B, GoldschmidtClass (T : Subgroup G) C B ∧ Nat.card C ≤ Nat.card B * ρ) ∧
      ∀ t ∈ (T : Subgroup G), orderOf t = 2 → (∃ g : G, g * t * g⁻¹ ∈ C) →
        Nat.card (⁅C, zpowers t⁆ : Subgroup G) ≤ ρ

@[expose] def AtlasL44Aut : Prop :=
  ∀ (E : Type) [Group E], Nonempty (E ≃* PSL(4, GaloisField 2 2)) →
    Nat.card (MulAut E) = 4 * Nat.card E

@[expose] def AtlasL44ThreeRank : Prop :=
  ∀ (E : Type) [Group E], Nonempty (E ≃* PSL(4, GaloisField 2 2)) →
    ∀ S : Subgroup E, (∀ s ∈ S, ∀ t ∈ S, s * t = t * s) → (∀ s ∈ S, s ^ 3 = 1) →
      Nat.card S ≤ 27

@[expose] def AtlasL44FixedPoints : Prop :=
  ∀ (E : Type) [Group E], Nonempty (E ≃* PSL(4, GaloisField 2 2)) →
    ∀ α : MulAut E, α * α = 1 → α ≠ 1 → 3 ≤ Nat.card {x : E // α x = x}

end CFSG.EvenSporadicStandard.M24Std
