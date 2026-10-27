module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop42CaseThreeProof

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs

@[expose] def Fi22WeakCore3 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], commutator Y = ⊤ → ∀ (N : Subgroup Y) [N.Normal],
    N ≤ Subgroup.center Y → IsFiTwentyTwo (Y ⧸ N) → ∀ P : Subgroup Y, IsPGroup 3 P →
      Nat.card P = 3 ^ (Nat.card Y).factorization 3 → (⊤ : Subgroup Y) ≤ weakCoreIn 3 P ⊤

@[expose] def Input24_7K : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K P : Subgroup G), CFSG.Open.IsKGroup ↥K →
    GLAPLayer 5 K = K → IsFiTwentyTwo (barOf 5 K) → P ≤ K → IsPGroup 3 P →
    Nat.card P = 3 ^ (Nat.card K).factorization 3 → K ≤ weakCoreIn 3 P K

end CFSG.HardMathSupport.Solomon.Coordinator
