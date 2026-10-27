module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435Chev.Classical

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435Chev

open TauCeti (PrimePower LieTypeIndex)

section Families


theorem familyAt_of_chevIndex (hD : ∀ q : PrimePower, q.p = 2 → FamilyAt (.twistedD 4 q))
    {d : LieTypeIndex} (hd : ChevIndex d) : FamilyAt d := by
  rcases hd with hd | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
  · cases d with
    | A r q => exact familyAt_A r q hd
    | twistedA r q => exact familyAt_twistedA r q hd
    | B r q => exact familyAt_B r q hd
    | C r q => exact familyAt_C r q hd
    | D r q => exact familyAt_D r q hd
    | twistedD r q =>
      rcases (show r = 4 ∨ 5 ≤ r ∨ r < 4 by omega) with rfl | hr | hr
      · exact hD q hd
      · exact familyAt_twistedD r q hd hr
      · intro hv
        have h4 := LieTypeIndex.four_le_of_twistedD_inStandardRange
          ((LieTypeIndex.valid_iff _).1 hv).1
        omega
    | E6 q => exact familyAt_E6 q hd
    | E7 q => exact familyAt_E7 q hd
    | E8 q => exact familyAt_E8 q hd
    | F4 q => exact familyAt_F4 q hd
    | G2 q => exact familyAt_G2 q hd
    | twistedE6 q => exact familyAt_twistedE6 q hd
    | trialityD4 q => exact familyAt_trialityD4 q hd
    | suzuki m => exact familyAt_suzuki m
    | reeG2 m => exact hd.elim
    | reeF4 m => exact familyAt_reeF4 m
    | tits => exact familyAt_tits
  · exact familyAt_L27 q hq
  · exact familyAt_U33 q hq

theorem kFact1435ChevTwo_of_twistedD4
    (hD : ∀ q : PrimePower, q.p = 2 → FamilyAt (.twistedD 4 q)) : KFact1435ChevTwo :=
  kFact1435ChevTwo_of_families fun _ hd => familyAt_of_chevIndex hD hd

end Families

end CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435Chev
