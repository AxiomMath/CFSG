
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Block
public import CFSG.Sporadic.J4.Local

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Sporadic.J4

@[expose] def J4HPart : Prop :=
  ∀ L : Subgroup ↥J, L ≤ Hj → D5Plus L → ⁅L, L⁆ = L →
    ∃ y : ↥J, orderOf y = 2 ∧ ∀ l ∈ L, l * y = y * l

end CFSG.QuasithinUnique.A5
