module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open

@[expose] def NoOddLinearThreeLStarF_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T K : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaximalLocal T K → quasithinIsFaithfulLocal T K →
    ∀ r : ℕ, r.Prime → 3 < r →
      ¬ IsPSL 3 r 1 (↥K ⧸ CFSG.pCore 2 ↥K) ∧ ¬ IsSL3 r (↥K ⧸ CFSG.pCore 2 ↥K)

end CFSG.Quasithin.H13.NQBlock
