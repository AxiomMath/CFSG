module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open

@[expose] def KFactSignalizerTrivial : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K → IsRankTwoSEGroup p K →
    ¬ Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group) →
    ∀ P : Sylow p K, ∀ W : Subgroup (MulAut K), Nat.Coprime p (Nat.card W) →
      (∀ g ∈ (P : Subgroup K), ∀ w ∈ W, MulAut.conj g * w * (MulAut.conj g)⁻¹ ∈ W) → W = ⊥

@[expose] def KFactWeakClosure : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X),
    K.Normal → IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K →
    Subgroup.centralizer (K : Set X) = ⊥ → p ∣ Nat.card K →
    ∀ Q : Sylow p X, K ⊔ (Q : Subgroup X) = ⊤ → IsMulCommutative (Q : Subgroup X) →
      2 ≤ CFSG.Open.pRank p ((Q : Subgroup X) ⊓ K) →
      ∀ A : Subgroup X, A ≤ (Q : Subgroup X) → Nat.card A = p →
        ∃ g : X, A.map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup X) ∧
          A.map (MulAut.conj g).toMonoidHom ≠ A

@[expose] def KFactInnerAction : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K → ∀ P : Sylow p K,
      (P : Subgroup K) ≠ ⊥ → IsMulCommutative (P : Subgroup K) →
      ∀ φ : MulAut K, (∃ n : ℕ, φ ^ (p ^ n) = 1) →
        (∀ g ∈ (P : Subgroup K), φ * MulAut.conj g = MulAut.conj g * φ) →
        ∃ g ∈ (P : Subgroup K), φ = MulAut.conj g

@[expose] def KFactCoprimeAutEvenCentralizer : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K → ¬ p ∣ Nat.card K →
    ∀ φ : MulAut K, φ ^ p = 1 → φ ≠ 1 → ∃ t : K, orderOf t = 2 ∧ φ t = t

structure GL83Generic5KFacts : Prop where
  signalizer : KFactSignalizerTrivial
  weakClosure : KFactWeakClosure
  innerAction : KFactInnerAction

end CFSG.LocalAnalysis.RankThreeTheoremC
