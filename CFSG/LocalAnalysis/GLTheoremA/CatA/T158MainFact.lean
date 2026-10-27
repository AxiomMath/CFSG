module

public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBetaK

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] def T158MainFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 →
    ∀ (K B : Subgroup X) (x₁ x₂ : X) (L₁ L₂ : Subgroup X),
      I158HypK p (⊤ : Subgroup X) K B x₁ x₂ L₁ L₂ →
      GLAPLayer p (L₁ ⊓ Subgroup.centralizer ({x₂} : Set X)) ≠ ⊥ →
        p = 3 ∧ ∃ n : ℕ, Odd n ∧ 1 < n ∧
          ((catalogIs (PSimple 3 K) (S10.isU6n n) ∧ catalogIs (PSimple 3 L₁) (S10.isL2n (3 * n)) ∧
              (∃ M : Subgroup X, GLAPComponent 3 (L₁ ⊓ Subgroup.centralizer ({x₂} : Set X)) M ∧
                catalogIs (PSimple 3 M) (S10.isL2n n)) ∧
              Nat.card B = 3 ^ 3 * Nat.card ↥(B ⊓ centModSubgroup 3 K)) ∨
            (catalogIs (PSimple 3 K) (S10.isTE6n n) ∧ catalogIs (PSimple 3 L₁) (S10.isU3n (3 * n)) ∧
              (∃ M : Subgroup X, GLAPComponent 3 (L₁ ⊓ Subgroup.centralizer ({x₂} : Set X)) M ∧
                catalogIs (PSimple 3 M) (S10.isU3n n)) ∧
              Nat.card B = 3 ^ 4 * Nat.card ↥(B ⊓ centModSubgroup 3 K))) ∧
          ∀ T : Subgroup X, T ≤ (⊤ : Subgroup X) → IsPGroup 2 T → B ≤ Subgroup.normalizer (T : Set X) →
            (⁅T, B⁆ : Subgroup X) = ⊥

end CFSG.LocalAnalysis.GLTheoremA.T158

end
