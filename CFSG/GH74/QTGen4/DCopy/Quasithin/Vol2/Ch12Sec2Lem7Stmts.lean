module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.Vol2.Ch12Sec2Setting

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Lem1227NotQuasisimple_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H X Y : Subgroup G), Hyp1223 G T L V →
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ Subgroup.normalizer (L : Set G) →
    IsHStar T (Subgroup.normalizer (L : Set G)) H → ¬ Group.IsSolvable ↥H → X ∈ cComp H →
    H = X ⊔ T → CFSG.IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X) → X ≤ Y →
    quasithinIsMaximalLocal T Y → quasithinIsFaithfulLocal T Y →
      CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y)

end CFSG.Quasithin.H13
