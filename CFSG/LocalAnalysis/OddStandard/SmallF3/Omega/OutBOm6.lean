module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutBOm6Aut

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82OddInnerOm6_holds :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G),
      ((IsQuasisimple L ∧ IsTwoU43 (L ⧸ oddCore L)) ∨ IsOm6P L ∨ IsOm6M L) → Asc82OddInner L := by
  intro G _ _ L h
  rcases h with ⟨hq, h⟩ | h | h
  · exact asc82OddInner_of_twoU43 hq h
  · exact asc82OddInner_of_isOm6P h
  · exact asc82OddInner_of_isOm6M h

end CFSG.OddStandard.SmallF3.Omega
