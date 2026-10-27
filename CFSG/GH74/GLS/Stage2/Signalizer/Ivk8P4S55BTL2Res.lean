module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTStmt

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

@[expose] def FL2Res : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S T Tstar : Subgroup G) (p : ℕ)
    (H P : Subgroup G) (g : G) (X Y : Subgroup G), Cfg55E G z k S T Tstar p H P g X Y →
    ∀ (t : G) (q : ℕ) (I Q₁ : Subgroup G), Data5A2 z k S T Tstar p H P t q I Q₁ →
    ∀ J : Subgroup (HBar H), BridgeB k p H P g J → FL2 (↥J ⧸ center ↥J) →
      barIn H I ≤ centralizer (J : Set (HBar H)) → False

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
