module

public import CFSG.LargeExtraspecial.S3Basic
public import CFSG.Open.TimmesfeldLargeExtraspecialMilestoneDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open
open scoped MatrixGroups

@[expose] def AschbacherSmith35Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), 3 ≤ S.width →
    (∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) →
      Nonempty (G ≃* timmesfeldPSU (S.width + 2)) ∨
        (S.width = 4 ∧ Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.Co2))

structure PattersonCo1Hyp (X : Type*) [Group X] [Finite X] (t : X) : Prop where
  simple : IsSimpleGroup X
  noncomm : ∃ a b : X, a * b ≠ b * a
  orderOf_eq : orderOf t = 2
  extraspecial : timmesfeldIsExtraspecial (timmesfeldFStar (centralizer ({t} : Set X)))
  card : Nat.card (timmesfeldFStar (centralizer ({t} : Set X))) = 2 ^ 9
  quotient : timmesfeldQuotientIso (timmesfeldFStar (centralizer ({t} : Set X)))
    (timmesfeldOmegaPlus 4)

@[expose] def PattersonCo1Input : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : X), PattersonCo1Hyp X t →
    Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Co1)

end CFSG.LargeExtraspecial.S14
