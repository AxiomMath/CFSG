module

public import Mathlib
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Assembly

export CFSG.Open (pCore pCoreOf IsElemAbelian pRank twoRank IsTwoLocal IsCharTwoType evenRank)

@[expose] def IsQuasisimple (G : Type*) [Group G] : Prop :=
  commutator G = ⊤ ∧ IsSimpleGroup (G ⧸ Subgroup.center G)

inductive IsSubnormal {G : Type*} [Group G] : Subgroup G → Subgroup G → Prop
  | refl (H : Subgroup G) : IsSubnormal H H
  | step {H M K : Subgroup G} : H ≤ M → (H.subgroupOf M).Normal → IsSubnormal M K →
      IsSubnormal H K

@[expose] def IsComponentOf {G : Type*} [Group G] (L K : Subgroup G) : Prop :=
  L ≤ K ∧ IsSubnormal L K ∧ IsQuasisimple L

@[expose] def oddCore (H : Type*) [Group H] : Subgroup H :=
  sSup {N : Subgroup H | N.Normal ∧ Odd (Nat.card N)}

instance oddCore_normal (H : Type*) [Group H] : (oddCore H).Normal :=
  Subgroup.sSup_normal _ fun _ hN => hN.1

@[expose] def IsComponentType (G : Type*) [Group G] : Prop :=
  ∃ t : G, orderOf t = 2 ∧
    ∃ L : Subgroup (Subgroup.centralizer ({t} : Set G) ⧸
        oddCore (Subgroup.centralizer ({t} : Set G))),
      IsComponentOf L ⊤

@[expose] def involutionGraph (G : Type*) [Group G] : SimpleGraph {t : G // orderOf t = 2} :=
  SimpleGraph.fromRel fun s t => (s : G) * t = t * s

end CFSG.Assembly
