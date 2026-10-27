module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Spor
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMathieu
public import CFSG.Sporadic.J1

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.RestrictedStd.Spor
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem m12_u42Free : SporadicU42Free .M12 :=
  sporadicU42Free_of_card CFSG.Sporadic.Mathieu.card_M12 (by norm_num)

theorem j1_u42Free : SporadicU42Free .J1 :=
  sporadicU42Free_of_card CFSG.Sporadic.J1.card_J1 (by norm_num)

theorem m23_u42Free :
    SporadicU42Free .M23 := by
  refine sporadicU42Free_of_comps isoInvariant_not_three_dvd isoInvariant_not_three_dvd
    u42_fails_not_three_dvd u42_fails_not_three_dvd (fun G _ _ ⟨e⟩ t ht =>
      compsSatisfy_centralizer_of_mulEquiv _ isoInvariant_not_three_dvd m23_centralizerIn_comps e
        t ht) (outer_comps_of_forall_inner (fun β => ?_) _)
  change β ∈ inner NativeSporadic.M23
  rw [CFSG.Sporadic.Schreier.inner_eq_top_of_card_le CFSG.Sporadic.Schreier.m23_center_eq_bot'
    CFSG.Sporadic.Schreier.m23_mulAut_card]
  trivial

theorem m24_u42Free :
    SporadicU42Free .M24 := by
  refine sporadicU42Free_of_comps isoInvariant_not_three_dvd isoInvariant_not_three_dvd
    u42_fails_not_three_dvd u42_fails_not_three_dvd (fun G _ _ ⟨e⟩ t ht =>
      compsSatisfy_centralizer_of_mulEquiv _ isoInvariant_not_three_dvd m24_centralizerIn_comps e
        t ht) (outer_comps_of_forall_inner (fun β => ?_) _)
  change β ∈ inner NativeSporadic.M24
  rw [CFSG.Sporadic.Schreier.inner_eq_top_of_card_le CFSG.Sporadic.Schreier.m24_center_eq_bot'
    CFSG.Sporadic.Schreier.m24_mulAut_card]
  trivial

end CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic
