module

public import CFSG.Quasithin.Background.C1PackS15212A
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace C1Pack12

section Standing

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T Mc M H B : Subgroup G}

theorem St12.of_stages_F4 (h5 : StageLemma15205_F4) (h1519 : StageLemma1519)
    (h15208 : StageLemma15208_F4) (h15209 : StageNotation15209_F4) (h15211 : StageLemma15211_F4)
    (hs : Setting152 T Mc M) (hH : IsHStar T M H) (hB : B ∈ sigmaPrime T H (V154 T Mc M)) :
    St12 T Mc M H B :=
  ⟨hs, hH, hB, h15208 G T Mc M hs H hH, h15209 G T Mc M hs H hH, h15211 G T Mc M hs H hH B hB,
    h1519 G T Mc M hs.qtfe hs.mf hs.ce, h5 G T Mc M hs⟩

end Standing

end C1Pack12

end CFSG.Quasithin
