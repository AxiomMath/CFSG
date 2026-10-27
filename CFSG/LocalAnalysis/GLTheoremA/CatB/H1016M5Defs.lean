module

public import CFSG.Open.GLADefs
public import CFSG.Sporadic.Schreier.Co1ThreeLocal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M5

open CFSG.Open

open scoped Matrix

@[expose] def TwoLocalRankCriterion : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p k m : ℕ), p.Prime → p ≠ 2 →
    (∀ j, 0 < j → j < m → ¬ 2 ^ j ≡ 1 [MOD p]) →
    (∀ t : X, orderOf t = 2 → ∀ E : Subgroup X, E ≤ Subgroup.centralizer ({t} : Set X) →
      IsElemAbelian p E → Nat.card E ≤ p ^ k) →
    (∀ F W : Subgroup X, IsElemAbelian p F → Nat.card F = p ^ k → IsElemAbelian 2 W →
      2 ^ m ≤ Nat.card W → F ≤ Subgroup.centralizer (W : Set X) → False) →
    GLATwoLocalRank p X ≤ k

@[expose] def Co1FiveCubeFacts : Prop :=
  (∀ E : Subgroup ↥CFSG.Sporadic.Co1Schreier.GA, IsElemAbelian 5 E → Nat.card E ≤ 5 ^ 3) ∧
    ∀ E : Subgroup ↥CFSG.Sporadic.Co1Schreier.GA, IsElemAbelian 5 E → Nat.card E = 5 ^ 3 →
      ∃ j ∈ E, ∀ v : Fin 24 → ZMod 2,
        ((j : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v → v = 0

@[expose] def BabyFiveRankFact : Prop :=
  ∀ E : Subgroup CFSG.Blueprint.NativeSporadic.B, IsElemAbelian 5 E → Nat.card E ≤ 5 ^ 3

end CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M5
