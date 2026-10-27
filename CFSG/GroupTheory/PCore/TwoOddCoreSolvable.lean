module

public import CFSG.Foundations.Basic
import CFSG.GroupTheory.ABGLocalTools.Constraint
import CFSG.GroupTheory.SolvableTransport
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.GroupTheory

theorem isSolvable_comap_oddCore_pCore_two (G : Type) [Group G] [Finite G] :
    Group.IsSolvable
      ((CFSG.oddCore (G ⧸ CFSG.pCore 2 G)).comap (QuotientGroup.mk' (CFSG.pCore 2 G))) := by
  have hB : Group.IsSolvable (CFSG.oddCore (G ⧸ CFSG.pCore 2 G)) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ CFSG.ABGLocalTools.odd_card_oddCore
  have hker : IsPGroup 2 (QuotientGroup.mk' (CFSG.pCore 2 G)).ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  exact isSolvable_comap_of_isPGroup_ker _ (QuotientGroup.mk'_surjective _) hB hker

theorem comap_oddCore_pCore_two_le_solvableRadical (G : Type) [Group G] [Finite G] :
    (CFSG.oddCore (G ⧸ CFSG.pCore 2 G)).comap (QuotientGroup.mk' (CFSG.pCore 2 G)) ≤
      CFSG.solvableRadical G :=
  le_sSup ⟨inferInstance, isSolvable_comap_oddCore_pCore_two G⟩

end CFSG.GroupTheory
