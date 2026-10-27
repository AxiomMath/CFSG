module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Pt

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def L28Shape (p : ℕ) {G : Type} [Group G] (P : Subgroup G) : Prop :=
  Nat.card P = p ^ 5 ∧
  ∃ Q₀ : Subgroup G, Q₀ < P ∧ (∀ R : Subgroup G, Q₀ < R → R ≤ P → R = P) ∧
    Nonempty (↥Q₀ ≃* (Multiplicative (ZMod (p ^ 2)) × Multiplicative (ZMod (p ^ 2)))) ∧
    (∃ C : Subgroup G, C ≤ P ∧ Q₀ ⊓ C = ⊥ ∧ Q₀ ⊔ C = P) ∧
    (∃ A B : Subgroup G, A ≠ ⊥ ∧ B ≠ ⊥ ∧ A ⊓ B = ⊥ ∧ A ⊔ B = Q₀ ∧
      P ≤ normalizer (A : Set G) ∧ P ≤ normalizer (B : Set G)) ∧
    ∀ a : G, a ∈ L28Z P ↔ a ∈ Q₀ ∧ a ^ p = 1

@[expose] def L28Shear (p : ℕ) {G : Type} [Group G] (P : Subgroup G) : Prop :=
  IsElemAbelian p (L28Z P) ∧
    ∀ u ∈ P, u ^ p = 1 → u ∉ L28Z P → ∀ z ∈ L28Z P, ∃ q ∈ P, q * u * q⁻¹ = u * z

@[expose] def L28Prop34S (p : ℕ) {G : Type} [Group G] [Finite G] (P : Sylow p G) (J : Subgroup G)
    (x : G) : Prop :=
  L28Prop34 p P J x ∧ L28Shape p (P : Subgroup G)

@[expose] def GL83GenericPrimeThreeL28Prop34S (G : Type) [Group G] [Finite G] : Prop :=
  GenericL28At G fun p P _ x J => L28Prop34S p P J x

end CFSG.LocalAnalysis.RankThreeTheoremC
