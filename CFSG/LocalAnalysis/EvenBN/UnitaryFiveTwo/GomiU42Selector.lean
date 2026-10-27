module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

structure GomiU42Data (X : Type) [Group X] [Finite X] (J D E : Subgroup X) (a : X) : Prop where
  kGroup : CFSG.SectionRank.IsKGroupCat X
  oddCore : CFSG.pPrimeCore 2 X = ⊥
  lieModel : CFSG.Blueprint.LieModel J .PSU 4 2 1
  standard : CFSG.IsStandardSubgroup J
  orderOf_a : orderOf a = 2
  inf_eq_bot : zpowers a ⊓ J = ⊥
  sup_eq : zpowers a ⊔ J = centralizer ({a} : Set X)
  not_central : ∀ S : Sylow 2 X, a ∈ S → ∃ s ∈ S, s * a ≠ a * s
  normalClosure_eq : normalClosure (J : Set X) = D
  simple : IsSimpleGroup D
  nonabelian : ∃ x y : D, x * y ≠ y * x
  lt : J < D
  centralizer_eq : centralizer (D : Set X) = ⊥
  catalog : CFSG.Blueprint.Catalog D
  elementary : CFSG.IsElementaryAbelian 2 E
  card_E : Nat.card E = 2 ^ 8
  mem_normalizer : a ∈ normalizer (E : Set X)
  card_centralizer_E : Nat.card (E ⊓ centralizer ({a} : Set X) : Subgroup X) = 2 ^ 4
  centralizer_E_le : E ⊓ centralizer ({a} : Set X) ≤ J

@[expose] def GomiU42Selector (P : (D : Type) → [Group D] → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (J D E : Subgroup X) (a : X),
    GomiU42Data X J D E a → P D → a ∉ D ∧ CFSG.Blueprint.LieModel D .PSL 4 2 2

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
