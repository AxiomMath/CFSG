module

public import CFSG.Blueprint.Catalog

public section

namespace CFSG.OddStandard.SmallF3.L33

open Subgroup CFSG.Blueprint

structure FritzHyp (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G) : Prop where
  orderOf_t : orderOf t = 2
  model : LieModel ↥L .PSL 3 3 1
  isSimple : IsSimpleGroup ↥L
  le_centralizer : L ≤ centralizer ({t} : Set G)
  le_normalizer : centralizer ({t} : Set G) ≤ normalizer (L : Set G)
  isCyclic_C : ∀ S : Sylow 2 ↥(centralizer (L : Set G)),
    IsCyclic (S : Subgroup ↥(centralizer (L : Set G)))
  isPGroup_K : IsPGroup 2 ↥(centralizer ({t} : Set G) ⊓ centralizer (L : Set G))
  not_sectRank4 : ¬ ∀ P : Subgroup G, IsPGroup 2 P →
    ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = P

end CFSG.OddStandard.SmallF3.L33
