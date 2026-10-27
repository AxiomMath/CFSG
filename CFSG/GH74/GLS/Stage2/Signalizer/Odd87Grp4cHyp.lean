module

public import CFSG.GH74.GLS.Stage2.Local.P27.FullStmt

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

@[expose] def NonCentralDihedral : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ x : G, IsNonCentralInvolution x → P27.FullG x

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
