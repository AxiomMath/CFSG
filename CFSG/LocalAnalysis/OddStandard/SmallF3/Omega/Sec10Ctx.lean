module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

structure Sec10Setting (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G) : Prop
    extends Sec3SettingLB G t L where
  psp4 : LieModel (L ⧸ oddCore L) .PSp 2 3 1

structure Sec10Z (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) : Prop
    extends Sec10Setting G t L, Asc82Notation t L S z

structure Sec10Ctx (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G)
    (K1 K2 : Subgroup G) : Prop extends Sec10Z G t L S z where
  pocket1 : Sl23PocketIn L z K1
  pocket2 : Sl23PocketIn L z K2
  ne : K1 ≠ K2

@[expose] def secQ (K1 K2 : Subgroup G) : Subgroup G :=
  twoCoreIn (K1 ⊔ K2)

@[expose] def secK0 (t z : G) : Subgroup G :=
  oTwoRes (centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G))

@[expose] def secW (t : G) (K1 K2 : Subgroup G) : Subgroup G :=
  secQ K1 K2 ⊔ zpowers t

@[expose] def secB (S L : Subgroup G) : Subgroup G :=
  JElem (S ⊓ L)

@[expose] def secA (t : G) (S L : Subgroup G) : Subgroup G :=
  secB S L ⊔ zpowers t

@[expose] def secM (t : G) (S L : Subgroup G) : Subgroup G :=
  normalizer (secA t S L : Set G)

end CFSG.OddStandard.SmallF3.Omega
