module

public import CFSG.Quasithin.H13.GoldschmidtM22EndN2b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6StatementsSec2

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin CFSG.QuasithinUnique.C5

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

section Conj

variable (h : Hyp6Sec2 G T M L V)

include h in

theorem CHU_le_normalizer_conj_V_F4 (hZ : Nat.card (quasithinOmegaOneCenter T) = 2)
    (h621 : Stmt6_2_1_F4) {g : G} (hg : g ∈ HH T) :
    CHU T L V ≤ Subgroup.normalizer ((conjSubgroup V g : Subgroup G) : Set G) := by
  refine (CHU_le_normalizer_conj_ZS h hZ hg).trans ?_
  rw [← CFSG.QuasithinUnique.C5.conjSubgroup_normalizer,
    ← CFSG.QuasithinUnique.C5.conjSubgroup_normalizer]
  exact CFSG.QuasithinUnique.C5.conjSubgroup_mono (h621 G T M L V h).1 g

end Conj

end CFSG.Quasithin.H13.GM22
