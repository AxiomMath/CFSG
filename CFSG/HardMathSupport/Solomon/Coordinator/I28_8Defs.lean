module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I28_8

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise

@[expose] noncomputable def thompsonJ {G : Type} [Group G] [Finite G] (S : Subgroup G) (i : ℕ) :
    Subgroup G :=
  ⨆ (B : Subgroup G) (_ : B ≤ S ∧ IsMulCommutative B ∧ CFSG.Open.pRank 2 S - i ≤ CFSG.Open.pRank 2 B), B

@[expose] def Th1Factorization : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R S : Subgroup G), Group.IsSolvable ↥R → ¬ 3 ∣ Nat.card R →
    ¬ 5 ∣ Nat.card R →
    (∀ N : Subgroup G, N ≤ R → R ≤ Subgroup.normalizer (N : Set G) → ¬ 2 ∣ Nat.card N → N = ⊥) →
    S ≤ R → IsPGroup 2 S → ¬ 2 ∣ S.relIndex R →
      ∀ i j : Fin 3, i ≠ j →
        ((Subgroup.normalizer (tripleOf S i : Set G) ⊓ R : Subgroup G) : Set G) *
          ((Subgroup.normalizer (tripleOf S j : Set G) ⊓ R : Subgroup G) : Set G) = (R : Set G)

@[expose] def L34Facts : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K T B : Subgroup Y), K.Normal → IsLThreeFour ↥K →
    IsPGroup 2 T → B ≤ Subgroup.normalizer (T : Set Y) → Nat.card ↥(B ⊓ K) = 9 →
    K ≤ Subgroup.centralizer (T : Set Y) ∨
      ∃ Q : Subgroup Y, Q ≤ K ∧ Nat.card Q = 7 ∧ T ≤ Subgroup.normalizer (Q : Set Y) ∧
        (∃ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ = q⁻¹) ∧
        (Subgroup.centralizer (T : Set Y) ⊓ K) ⊔ Q = K

@[expose] def Th1FactorizationTwoSeven : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R S : Subgroup G), Group.IsSolvable ↥R →
    (∀ p : ℕ, p.Prime → p ∣ Nat.card R → p = 2 ∨ p = 7) →
    (∀ N : Subgroup G, N ≤ R → R ≤ Subgroup.normalizer (N : Set G) → ¬ 2 ∣ Nat.card N → N = ⊥) →
    S ≤ R → IsPGroup 2 S → ¬ 2 ∣ S.relIndex R →
      ∀ (D : Type) [Group D] (ρ : G →* D) (Q : Subgroup D), Nat.card Q = 7 →
        S.map ρ ≤ Subgroup.normalizer (Q : Set D) →
        (∃ t ∈ S, ∀ q ∈ Q, ρ t * q * (ρ t)⁻¹ = q⁻¹) → R.map ρ = S.map ρ ⊔ Q →
          ∃ s : Finset (Fin 3), 2 ≤ s.card ∧ ∀ i ∈ s,
            Q ≤ (Subgroup.normalizer (tripleOf S i : Set G) ⊓ R).map ρ

@[expose] def Th1J1Factorization : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R S : Subgroup G), Group.IsSolvable ↥R → ¬ 3 ∣ Nat.card R →
    ¬ 5 ∣ Nat.card R →
    (∀ N : Subgroup G, N ≤ R → R ≤ Subgroup.normalizer (N : Set G) → ¬ 2 ∣ Nat.card N → N = ⊥) →
    S ≤ R → IsPGroup 2 S → ¬ 2 ∣ S.relIndex R →
      ∀ i : Fin 3, i ≠ 1 →
        ((Subgroup.normalizer (tripleOf S i : Set G) ⊓ R : Subgroup G) : Set G) *
          ((Subgroup.normalizer (tripleOf S 1 : Set G) ⊓ R : Subgroup G) : Set G) = (R : Set G)

end CFSG.HardMathSupport.Solomon.Coordinator.I28_8
