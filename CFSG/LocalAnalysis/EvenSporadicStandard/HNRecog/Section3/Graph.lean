module

public import CFSG.Monster.GMS.TwoAGraph
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog CFSG.Monster.GMS

variable {G : Type} [Group G]

abbrev Gamma (a : G) : SimpleGraph (ConjVert a) := twoAGraph a

theorem gamma_adj_iff {a : G} {x y : ConjVert a} :
    (Gamma a).Adj x y ↔ x ≠ y ∧ IsConj a ((x : G) * y) :=
  Iff.rfl

@[expose] def gammaPerp (a : G) (S : Set G) : Set G :=
  {y | IsConj a y ∧ ∀ x ∈ S, y = x ∨ (x ≠ y ∧ IsConj a (x * y))}

@[expose] def IsLine (a : G) (l : Set G) : Prop :=
  (∀ x ∈ l, IsConj a x) ∧ l.ncard = 3 ∧ Nonempty (↥(Subgroup.closure l) ≃* Elem2 2)

end CFSG.EvenSporadicStandard.HNRecog.Section3
