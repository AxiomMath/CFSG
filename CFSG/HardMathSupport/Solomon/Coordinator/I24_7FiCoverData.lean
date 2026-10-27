module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open

@[expose] def Fi22CoverData (M : Type*) [Group M] [Finite M] : Prop :=
  ∃ (P0 E5 Q4 : Subgroup M) (n5 n4 n4' : M),
    IsPGroup 3 P0 ∧ Nat.card P0 = 3 ^ (Nat.card M).factorization 3 ∧
    E5 ≤ P0 ∧ IsElemAbelian 3 E5 ∧ Nat.card E5 = 3 ^ 5 ∧
    Q4 ≤ P0 ∧ IsElemAbelian 3 Q4 ∧ Nat.card Q4 = 3 ^ 4 ∧
    n5 ∈ Subgroup.normalizer (E5 : Set M) ∧ n4 ∈ Subgroup.normalizer (Q4 : Set M) ∧
    n4' ∈ Subgroup.normalizer (Q4 : Set M) ∧ Subgroup.closure ({n5, n4, n4'} : Set M) = ⊤

end CFSG.HardMathSupport.Solomon.Coordinator
