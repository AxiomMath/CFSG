module

public import CFSG.CGT.PushingUp.Defs
public import CFSG.CGT.PushingUpLit.BlocksCommutePrime3
public import CFSG.CGT.PushingUpLit.LIT.FooteSplit

public section

namespace CFSG.CGT.PushingUpLit.A4

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly

section Defs

variable {G : Type} [Group G]

@[expose] def TwoConj (M X : Subgroup G) (m : G) : Prop :=
  m ∈ M ∧ conjSub m X ≠ X ∧ ∀ k ∈ M, conjSub k X = X ∨ conjSub k X = conjSub m X

@[expose] def baseTwo (X : Subgroup G) (m : G) : Subgroup G :=
  pCoreOf 2 X ⊔ pCoreOf 2 (conjSub m X)

@[expose] def StrongClosureTwo (M X : Subgroup G) (m : G) : Prop :=
  ∀ g : G, conjSub g (baseTwo X m) ≤ M → g ∈ M

@[expose] def Lemma34Two (M : Subgroup G) : Prop :=
  ∀ U : Subgroup G, U ≤ M → IsKleinFour ↥U → ∀ g : G,
    (∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ conjSub g M) → g ∈ M

end Defs

end CFSG.CGT.PushingUpLit.A4
