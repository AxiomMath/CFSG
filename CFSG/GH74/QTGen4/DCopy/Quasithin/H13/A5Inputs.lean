module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Background.G2A5Setting
public import CFSG.Quasithin.H13.StatementsFSU

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

@[expose] def Stmt13_3_2_three_A5_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L : Subgroup G), QTH13 G T L →
    ∀ K : Subgroup G, quasithinIsFaithfulLocal T K →
      quasithinO2QuotientIso K (alternatingGroup (Fin 5)) →
      ∀ V : Subgroup G, IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T V →
        IsA5ModuleFor K (Subgroup.centralizer (V : Set G)) V

end CFSG.Quasithin.H13
