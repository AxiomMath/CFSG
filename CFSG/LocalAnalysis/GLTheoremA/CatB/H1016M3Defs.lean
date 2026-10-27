module

public import CFSG.Open.LocalVocabulary
public import CFSG.Sporadic.Schreier.Co1ThreeLocal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3

open CFSG.Open

open scoped Matrix

@[expose] def Co1ThreeRankFact : Prop :=
  ∀ E : Subgroup ↥CFSG.Sporadic.Co1Schreier.GA, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 6

@[expose] def BabyThreeRankFact : Prop :=
  ∀ E : Subgroup CFSG.Blueprint.NativeSporadic.B, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 6

@[expose] def Co1ThreeSixFixFact : Prop :=
  ∀ E : Subgroup ↥CFSG.Sporadic.Co1Schreier.GA, IsElemAbelian 3 E → Nat.card E = 3 ^ 6 →
    ∃ j ∈ E, ∀ v : Fin 24 → ZMod 2,
      ((j : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v → v = 0

end CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3
