module

public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] def I2315aAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ K Qo : Subgroup G, IsChev2 K → IsPGroup q Qo → Qo ≤ K →
    (∀ Q : Subgroup G, IsPGroup q Q → Q ≤ K → Qo ≤ Q → Q = Qo) → 4 ≤ GLATwoLocalRank q ↥K →
    K ≤ sSup {N | ∃ X : Subgroup G, X ≤ Qo ∧ 2 ≤ CFSG.Open.pRank q X ∧
      3 ≤ CFSG.Open.pRank q (X ⊔ (Qo ⊓ Subgroup.centralizer (X : Set G))) ∧
      N = Subgroup.normalizer (X : Set G) ⊓ K}

@[expose] def I2315bAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p q : ℕ, p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p → ∀ W K V M Fo : Subgroup G,
    GLAPComponent p W K → IsChevSimple 2 (PSimple p K) → W ≤ Subgroup.normalizer (K : Set G) →
    Nat.Coprime q (Nat.card V) → V ≤ K → W ≤ Subgroup.normalizer (V : Set G) →
    (⁅K, GLAPPrimeCoreOf p K⁆ : Subgroup G) ≤ V →
    IsPGroup q Fo → Fo ≤ W → (∀ Q : Subgroup G, IsPGroup q Q → Q ≤ W → Fo ≤ Q → Q = Fo) →
    3 ≤ CFSG.Open.pRank q Fo →
    (∀ X : Subgroup G, X ≤ Fo → 2 ≤ CFSG.Open.pRank q X →
      3 ≤ CFSG.Open.pRank q (X ⊔ (Fo ⊓ Subgroup.centralizer (X : Set G))) →
      Subgroup.normalizer (X : Set G) ⊓ W ≤ M) →
    pCoreOf 2 M ⊓ K ≤ GLAPPrimeCoreOf p K

@[expose] def I3013At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p q : ℕ) (X K : Subgroup G), p.Prime → q.Prime → q ≠ 2 → CFSG.Open.IsKGroup ↥X → GLAPComponent p X K →
    IsChevSimple 2 (PSimple p K) → S9.InvolvedSL2 q (PSimple p K) →
    Nat.card (PSimple p K) = 60 ∨ Nat.card (PSimple p K) = 168

@[expose] def E62At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (L : Subgroup G), p.Prime → p ≠ 2 → LabelOf L ⟨.E6, 0, 1⟩ → HalfSplit16At p L → NoSplit16 p L →
    GLATwoLocalRank p ↥L ≤ 2

end CFSG.LocalAnalysis.GLTheoremA
