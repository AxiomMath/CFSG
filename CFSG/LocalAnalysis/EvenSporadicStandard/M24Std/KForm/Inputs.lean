module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Input
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.Open.FusionDefs

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped MatrixGroups

abbrev egQD {G : Type} [Group G] (D : Subgroup G) : Type :=
  normalizer (D : Set G) ⧸ D.subgroupOf (normalizer (D : Set G))

@[expose] def Ega81HypAZ2A8K : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.SectionRank.IsKGroupCat X →
    ∀ (z : X) (H : Subgroup X), orderOf z = 2 → Nonempty (H ≃* alternatingGroup (Fin 8)) →
      centralizer ({z} : Set X) = H ⊔ zpowers z → z ∈ centralizer (H : Set X) →
      Nonempty (egaLayer (X ⧸ fusionOddCore X) ≃* alternatingGroup (Fin 8)) ∨
      Nonempty (egaLayer (X ⧸ fusionOddCore X) ≃*
        alternatingGroup (Fin 8) × alternatingGroup (Fin 8)) ∨
      Nonempty (egaLayer (X ⧸ fusionOddCore X) ≃* alternatingGroup (Fin 10)) ∨
      Nonempty (egaLayer (X ⧸ fusionOddCore X) ≃* PSL(4, GaloisField 2 2)) ∨
      IsSporadic (egaLayer (X ⧸ fusionOddCore X)) .HS

@[expose] def CLayerDisjIso (X : Type) [Group X] [Finite X] : Prop :=
  Nonempty (egaLayer (X ⧸ fusionOddCore X) ≃* alternatingGroup (Fin 6)) ∨
    Nonempty (egaLayer (X ⧸ fusionOddCore X) ≃*
      alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) ∨
    Nonempty (egaLayer (X ⧸ fusionOddCore X) ≃* alternatingGroup (Fin 8)) ∨
    LieModel (egaLayer (X ⧸ fusionOddCore X)) .PSU 4 2 1 ∨
    LieModel (egaLayer (X ⧸ fusionOddCore X)) .PSL 5 2 1 ∨
    LieModel (egaLayer (X ⧸ fusionOddCore X)) .PSU 5 2 1 ∨
    LieModel (egaLayer (X ⧸ fusionOddCore X)) .PSp 2 2 2 ∨
    LieModel (egaLayer (X ⧸ fusionOddCore X)) .PSU 4 3 1

@[expose] def HarrisSolomonZ2S6IsoK : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.SectionRank.IsKGroupCat X → ∀ z : X, orderOf z = 2 →
    Nonempty (↥(centralizer ({z} : Set X)) ⧸ fusionOddCore ↥(centralizer ({z} : Set X)) ≃*
      Multiplicative (ZMod 2) × Equiv.Perm (Fin 6)) →
    CLayerDisjIso X

@[expose] def KLocalSections (G : Type) [Group G] : Prop :=
  ∀ D : Subgroup G, D ≠ ⊥ → (∀ x ∈ D, ∀ y ∈ D, x * y = y * x) →
    CFSG.SectionRank.IsKGroupCat (egQD D)

theorem KLocalSections.of_isKGroupCat {G : Type} [Group G] (h : CFSG.SectionRank.IsKGroupCat G) :
    KLocalSections G := fun D _ _ =>
  (h.subgroup (normalizer (D : Set G))).quotient (D.subgroupOf (normalizer (D : Set G)))

end CFSG.EvenSporadicStandard.M24Std
