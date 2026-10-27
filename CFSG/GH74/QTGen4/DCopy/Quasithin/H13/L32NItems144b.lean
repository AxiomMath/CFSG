module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.H13.L32NStatements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

@[expose] def Lemma1444CTL_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14310One G T L V →
    CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V) → Nat.card ↥(fsuU T V) = 2 ^ 5 →
    ¬ LieModel G .G2 0 3 1 → T ⊓ Subgroup.centralizer (L : Set G) = ⊥

end CFSG.Quasithin.H13
