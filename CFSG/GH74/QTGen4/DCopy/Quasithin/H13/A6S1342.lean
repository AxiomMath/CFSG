module

public import CFSG.Quasithin.H13.A6S1342
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

namespace Setting134

variable (S : Setting134 G T L V)
include S

theorem normalizer_L_le_F4 (h1222 : Stmt12_2_2_F4) :
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  rcases h1222 G T S.h13.simple S.h13.nonabelian S.h13.qtke S.h13.sylow with h | h
  · exact absurd h S.not_alt12_2_2
  · rcases ((h L S.maximal S.h13.faithful S.fsu.quasisimple).2.2 V S.irr).2.2.1 with h' | h'
    · exact h'
    · exact absurd h' S.zv

theorem lemma13_4_2_one_F4 (h1222 : Stmt12_2_2_F4) :
    Subgroup.normalizer (L : Set G) = Subgroup.normalizer (V : Set G) ∧
      Subgroup.normalizer (V : Set G) =
        Subgroup.centralizer ((V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
  ⟨le_antisymm (S.normalizer_L_le_F4 h1222) S.normalizer_V_le,
    le_antisymm S.normalizer_V_le_centralizer_ZV (S.centralizer_ZV_le.trans
      (S.normalizer_L_le_F4 h1222))⟩

end Setting134

end CFSG.Quasithin.H13.A6
