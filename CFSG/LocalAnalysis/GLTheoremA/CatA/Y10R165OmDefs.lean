module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Concl

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.RankThree.Classical2

instance finite_linearEquiv_self {F W : Type*} [Field F] [Finite F] [AddCommGroup W]
    [Module F W] [FiniteDimensional F W] : Finite (W ≃ₗ[F] W) :=
  haveI : Finite W := Module.finite_of_finite F
  Finite.of_injective (fun g : W ≃ₗ[F] W => (g : W → W)) fun _ _ h => LinearEquiv.ext (congrFun h)

@[expose] def OmTorusThree : Prop :=
  ∀ (F W : Type) [Field F] [Finite F] [CharP F 2] [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (Q : QuadraticForm F W),
    (QuadraticMap.polarBilin Q).Nondegenerate → 8 ≤ Module.finrank F W →
    ∀ q : ℕ, q.Prime → q ≠ 2 → (q ∣ Nat.card F - 1 ∨ q ∣ Nat.card F + 1) →
      ∃ T : Subgroup (W ≃ₗ[F] W), T ≤ orthDerived Q ∧ IsElemAbelian q T ∧
        3 ≤ CFSG.Open.pRank q T

@[expose] def OmHypRankLower : Prop :=
  ∀ (F W : Type) [Field F] [Finite F] [CharP F 2] [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (Q : QuadraticForm F W) (k : ℕ)
    (P : Fin (2 * k) → CFSG.ClassicalGroups.Orthogonal.HypPair Q),
    (∀ i j, i ≠ j → (P i).Orth (P j)) →
    ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ Nat.card F + 1 →
      2 * k ≤ CFSG.Open.pRank r (⊤ : Subgroup ↥(orthDerived Q))

@[expose] def Om165Engine : Prop :=
  ∀ (F V : Type) [Field F] [Finite F] [CharP F 2] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V),
    (QuadraticMap.polarBilin Q).Nondegenerate →
    ∀ n p q : ℕ, Nat.card F = 2 ^ n → p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
      (q ∣ 2 ^ n - 1 ∨ q ∣ 2 ^ n + 1) →
      ∀ Ã : Subgroup ↥(orthDerived Q), IsElemAbelian p Ã →
        CFSG.Open.pRank p (⊤ : Subgroup ↥(orthDerived Q)) ≤ CFSG.Open.pRank p Ã →
        3 ≤ CFSG.Open.pRank p Ã →
        (3 ≤ rk2Ord p n ∨ (rk2Ord p n = 2 ∧ ∃ ℓ : ℕ, Module.finrank F V = 2 * ℓ ∧ Odd ℓ ∧
          5 ≤ ℓ ∧ ℓ - 1 ≤ CFSG.Open.pRank p Ã)) →
        Concl165 ↥(orthDerived Q) p q Ã

end CFSG.LocalAnalysis.GLTheoremA.Y10F
