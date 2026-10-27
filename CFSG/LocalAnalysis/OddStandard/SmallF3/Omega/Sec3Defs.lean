module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def IsSL23Mod (Q : Type) [Group Q] : Prop :=
  Nonempty (Q ⧸ oddCore Q ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))

@[expose] def Sl23PocketIn (X : Subgroup G) (y : G) (K : Subgroup G) : Prop :=
  y ∈ K ∧ K ≤ X ⊓ centralizer ({y} : Set G) ∧
    (K.subgroupOf (X ⊓ centralizer ({y} : Set G))).IsSubnormal ∧ IsSL23Mod K

@[expose] def Sl23Pocket (x y : G) (K : Subgroup G) : Prop :=
  Sl23PocketIn (centralizer ({x} : Set G)) y K

@[expose] def IsI4PlusIn (X : Subgroup G) (y : G) : Prop :=
  orderOf y = 2 ∧ ∃ K : Subgroup G, Sl23PocketIn X y K

@[expose] def IsLnEps3 (I : Subgroup G) : Prop :=
  ∃ n : ℕ, LieModel (I ⧸ oddCore I) .PSL n 3 1 ∨ LieModel (I ⧸ oddCore I) .PSU n 3 1

@[expose] def IsL3Eps3 (I : Subgroup G) : Prop :=
  LieModel (I ⧸ oddCore I) .PSL 3 3 1 ∨ LieModel (I ⧸ oddCore I) .PSU 3 3 1

@[expose] def AschLBalance (G : Type) [Group G] : Prop :=
  ∀ u y : G, orderOf u = 2 → orderOf y = 2 → u * y = y * u →
    ∀ J : Subgroup G, IsComponentIn J (centralizer ({u, y} : Set G)) →
      ∃ K : Subgroup G, IsComponentIn K (centralizer ({y} : Set G)) ∧
        J ≤ K ⊔ CFSG.conjugate K u

end CFSG.OddStandard.SmallF3.Omega
