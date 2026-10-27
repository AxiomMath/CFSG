module

public import CFSG.Open.GLBDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

@[expose] def D1UniqueOverJ (p : ℕ) (H R J : Subgroup G) : Prop :=
  ∀ H' : Subgroup G, GLBIsMaxTwoLocal H' → J ≤ H' → ∀ Y : Subgroup G, Y ≤ H' → IsPGroup p Y →
    Nat.card R ≤ Nat.card Y → Open.pRank p R ≤ Open.pRank p Y → H' = H

end CFSG.AGLEmbedding
