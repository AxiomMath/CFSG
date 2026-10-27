module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open CFSG.Open
open scoped commutatorElement

@[expose] def SylowDichotomyAt (K : Type) [Group K] [Finite K] (p : ℕ) : Prop :=
  (Nat.card K).factorization p ≤ 3 ∨ (∀ S : Sylow p K, IsMulCommutative (S : Subgroup K)) ∨
    CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 2 ∨
    ∃ U : Subgroup K, IsPGroup p U ∧ (4 ≤ CFSG.Open.pRank p U ∨ ¬ IsCyclic ↥⁅U, U⁆ ∨
      ((∀ u ∈ U, u ^ p = 1) ∧ p ^ 5 ≤ Nat.card U))

@[expose] def SylowDichotomy : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ (p : ℕ), p.Prime → 5 ≤ p → p ∣ Nat.card K → SylowDichotomyAt K p

@[expose] def SDAlt : Prop :=
  ∀ n : ℕ, 5 ≤ n → ∀ p : ℕ, p.Prime → 5 ≤ p → SylowDichotomyAt (alternatingGroup (Fin n)) p

@[expose] def SDLie : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n ℓ f : ℕ),
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n ℓ f → CFSG.Blueprint.LieModel K t n ℓ f →
      ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ Nat.card K → SylowDichotomyAt K p

@[expose] def SDSpor : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    CFSG.Blueprint.NativeSporadic.SporadicRep K → ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ Nat.card K →
      SylowDichotomyAt K p

@[expose] def OuterHeisInner : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ (p : ℕ), p.Prime → 5 ≤ p → p ∣ Nat.card K →
    ∀ S : Sylow p K, (IsMulCommutative (S : Subgroup K) ∨ (Nat.card K).factorization p ≤ 3) →
      ∀ α : MulAut K, α ^ p = 1 → (∀ s ∈ (S : Subgroup K), α s = s) →
        α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner K

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
