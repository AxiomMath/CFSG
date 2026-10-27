module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeUC.GN15JOutCentralAtDef
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem jOutCentralAt_of_isSolvable_quotient {X : Type} [Group X] [Finite X] {T : Subgroup X}
    (h : Group.IsSolvable (X ⧸ gnC T)) : JOutCentralAt T := by
  intro L hL hne
  exfalso
  have := h
  have : Group.IsSolvable ↥L :=
    Group.isSolvable_of_isSolvable_injective (f := L.subtype) L.subtype_injective
  have hLbot : L ≠ ⊥ := by
    rintro rfl
    exact hne (Subgroup.commutator_bot_left _)
  have : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).mpr hLbot
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥L).ne hL.2.2.1

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15

end
