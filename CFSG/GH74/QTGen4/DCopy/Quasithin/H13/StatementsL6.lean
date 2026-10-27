module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.H13.StatementsFSU

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped IsMulCommutative Pointwise Matrix

@[expose] def Stmt3_2_14_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsLocal T L → ¬ CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
      (CFSG.solvableRadical ↥L).map L.subtype ≤
        Subgroup.centralizer (reducedAggregate (L ⊔ T) : Set G)

end CFSG.Quasithin.H13
