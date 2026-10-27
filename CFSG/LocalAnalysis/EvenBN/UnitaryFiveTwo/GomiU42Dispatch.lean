module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Selector
import CFSG.Milestones.CT_catalog_nonabelian_type_partition

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open CFSG.Blueprint

theorem gomiU42Selector_of_families
    (hAlt : GomiU42Selector fun D _ => ∃ m : ℕ, 5 ≤ m ∧ Nonempty (D ≃* alternatingGroup (Fin m)))
    (hOdd : GomiU42Selector fun D _ => OddLieType D)
    (hEven : GomiU42Selector fun D _ => EvenLieType D)
    (hSpor : GomiU42Selector fun D _ => NativeSporadic.SporadicRep D) :
    GomiU42Selector fun _ _ => True := by
  intro X _ _ J D E a h _
  rcases (CFSG.Milestones.ct_catalog_nonabelian_type_partition D h.nonabelian).1 h.catalog with
    hp | hp | hp | hp
  · exact hAlt X J D E a h hp
  · exact hOdd X J D E a h hp
  · exact hEven X J D E a h hp
  · exact hSpor X J D E a h hp

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
