module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily

public section

namespace CFSG.QuasithinUnique.K1

@[expose] def TitsNoStronglyClosedElemAbelian : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Blueprint.ReeTitsModel X .Tits 2 1 →
    NoStronglyClosedElemAbelian X

@[expose] def TitsSylowCentralizingAutInner : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Blueprint.ReeTitsModel X .Tits 2 1 →
    SylowCentralizingAutInner X

theorem centralizes_of_tits (hX : TitsNoStronglyClosedElemAbelian)
    (hA : TitsSylowCentralizingAutInner) {G : Type} [Group G] [Finite G] {H S U L : Subgroup G}
    (h : StrongClosureComponent H S U L)
    (hmodel : CFSG.Blueprint.ReeTitsModel (L ⧸ Subgroup.center L) .Tits 2 1) {w : G}
    (hwU : w ∈ U) (hwS : w ∈ Subgroup.centralizer (S : Set G)) :
    L ≤ Subgroup.centralizer ({w} : Set G) :=
  centralizes_of_family h (hX _ hmodel) (hA _ hmodel) hwU hwS

end CFSG.QuasithinUnique.K1
