module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Spor
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCaseJ4
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCo3
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMathieu
public import CFSG.Sporadic.Schreier.J4SNoComp
public import CFSG.Sporadic.SmallOddCore.Co3Aut

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.RestrictedStd.Spor
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem m11_u42Free :
    SporadicU42Free .M11 := by
  have hU := u42_fails_card_dvd (c := 48) (by norm_num)
  refine sporadicU42Free_of_comps (isoInvariant_card_dvd 48) (isoInvariant_card_dvd 48) hU
    hU (fun G _ _ ⟨e⟩ t ht => compsSatisfy_centralizer_of_mulEquiv _ (isoInvariant_card_dvd 48)
      m11_centralizerIn_comps e t ht) (outer_comps_of_forall_inner (fun β => ?_) _)
  change β ∈ inner NativeSporadic.M11
  rw [CFSG.Sporadic.Schreier.inner_eq_top_of_card_le CFSG.Sporadic.Schreier.m11_center_eq_bot'
    CFSG.Sporadic.Schreier.m11_mulAut_card]
  trivial

theorem m22_u42Free :
    SporadicU42Free .M22 := by
  refine sporadicU42Free_of_comps (isoInvariant_card_dvd 384) isoInvariant_not_three_dvd
    (u42_fails_card_dvd (c := 384) (by norm_num)) u42_fails_not_three_dvd
    (fun G _ _ ⟨e⟩ t ht => compsSatisfy_centralizer_of_mulEquiv _
      (isoInvariant_card_dvd 384) m22_centralizerIn_comps e t ht)
    (fun G _ _ _ ⟨e⟩ β hβ2 hβ => ?_)
  exact CompsSatisfy.of_mulEquiv isoInvariant_not_three_dvd (fixSubTransportEquiv e β)
    (m22_outer_comps _ (transportAut_mul_self e (mul_self_eq_one_of_orderOf_eq_two hβ2))
      (transportAut_not_mem_inner e hβ))

theorem j4_u42Free :
    SporadicU42Free .J4 := by
  refine sporadicU42Free_of_comps (Qi := fun _ _ => False) (Qo := fun _ _ => False)
    (fun _ _ _ _ _ h => h) (fun _ _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    (fun _ _ _ _ _ h => h) (fun G _ _ hG t ht B hB => j4NoComponentsInput G hG t ht B hB)
    (fun G _ _ _ ⟨e⟩ β hβ2 hβ => ?_)
  exfalso
  have eJ : G ≃* CFSG.Sporadic.J4.J :=
    e.trans (CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat)
  have hcard : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer G) =
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer CFSG.Sporadic.J4.J) :=
    @CFSG.Sporadic.J4Schreier.card_outer_congr G CFSG.Sporadic.J4.J _
      (Subgroup.toGroup CFSG.Sporadic.J4.J) eJ
  have hodd : Odd (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer G)) := by
    rw [hcard]
    exact CFSG.Sporadic.J4Schreier.CTU_J4_outer_automorphism_group_odd_order
  exact hβ (mem_inner_of_odd_card_outer hodd (mul_self_eq_one_of_orderOf_eq_two hβ2))

theorem co3_u42Free :
    SporadicU42Free .Co3 := by
  have hU := u42_fails_card_quotient_center_mem (N := co3Orders) (by simp [co3Orders])
  refine sporadicU42Free_of_comps (isoInvariant_card_quotient_center _)
    (isoInvariant_card_quotient_center _) hU hU (fun G _ _ ⟨e⟩ t ht => co3_inner_comps e t ht)
    (outer_comps_of_forall_inner (s := .Co3) (fun β => ?_) _)
  obtain ⟨g, hg⟩ := CFSG.Sporadic.SmallOddCore.ctuc_co3_all_automorphisms_inner.{0}.2.1.1 β
  exact ⟨g, hg.symm⟩

end CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic
