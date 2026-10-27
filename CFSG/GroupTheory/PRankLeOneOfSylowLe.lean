module

public import CFSG.GroupTheory.PRankLeOfSylowLe

public section

namespace CFSG

open CFSG.ABGLocalTools

theorem pRank_le_one_of_isSylowOf_le {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {Y N₁ S : Subgroup X} (hSY : S ≤ Y) (hSyl : IsSylowOf p S Y) (hSN : S ≤ N₁)
    (hN : CFSG.Open.pRank p N₁ ≤ 1) : CFSG.Open.pRank p Y ≤ 1 :=
  Nat.le_trans (pRank_le_of_isSylowOf_le hp hSY hSyl hSN) hN

end CFSG

end
