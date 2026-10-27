module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporSmall
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMathieu

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu
open CFSG.ComponentClassification.OuterAutomorphisms

theorem not_isSmallOrder_dvd_48 : ∀ N, IsSmallOrder N → ¬ N ∣ 48 :=
  not_isSmallOrder_dvd (q₁ := 5) (by norm_num) (by norm_num) (by decide) (by norm_num)
    (by norm_num)

theorem not_isSmallOrder_dvd_384 : ∀ N, IsSmallOrder N → ¬ N ∣ 384 :=
  not_isSmallOrder_dvd (q₁ := 11) (by norm_num) (by norm_num) (by decide) (by norm_num)
    (by norm_num)

theorem sporadicCase_M11 : SporadicCase .M11 := by
  refine sporadicCase_of_comps (fun G _ _ ⟨e⟩ t ht => ?_) (outer_of_forall_inner fun α => ?_)
  · exact (compsSatisfy_centralizer_of_mulEquiv _ (isoInvariant_card_dvd 48)
      m11_centralizerIn_comps e t ht).mono fun Y _ h => not_small_of_card_dvd
        not_isSmallOrder_dvd_48 h
  · change α ∈ inner NativeSporadic.M11
    rw [inner_eq_top_of_card_le m11_center_eq_bot' m11_mulAut_card]
    trivial

theorem sporadicCase_M22 : SporadicCase .M22 := by
  refine sporadicCase_of_comps (fun G _ _ ⟨e⟩ t ht => ?_) (fun G _ _ _ _ ⟨e⟩ α hα2 hα => ?_)
  · exact (compsSatisfy_centralizer_of_mulEquiv _ (isoInvariant_card_dvd 384)
      m22_centralizerIn_comps e t ht).mono fun Y _ h => not_small_of_card_dvd
        not_isSmallOrder_dvd_384 h
  · refine CompsSatisfy.of_mulEquiv isoInvariant_not_small (fixSubTransportEquiv e α) ?_
    exact (m22_outer_comps _ (transportAut_mul_self e hα2)
      (transportAut_not_mem_inner e hα)).mono fun Y _ h => not_small_of_not_three h

theorem sporadicCase_M23 : SporadicCase .M23 := by
  refine sporadicCase_of_comps (fun G _ _ ⟨e⟩ t ht => ?_) (outer_of_forall_inner fun α => ?_)
  · exact (compsSatisfy_centralizer_of_mulEquiv _ isoInvariant_not_three_dvd
      m23_centralizerIn_comps e t ht).mono fun Y _ h => not_small_of_not_three h
  · change α ∈ inner NativeSporadic.M23
    rw [inner_eq_top_of_card_le m23_center_eq_bot' m23_mulAut_card]
    trivial

theorem sporadicCase_M24 : SporadicCase .M24 := by
  refine sporadicCase_of_comps (fun G _ _ ⟨e⟩ t ht => ?_) (outer_of_forall_inner fun α => ?_)
  · exact (compsSatisfy_centralizer_of_mulEquiv _ isoInvariant_not_three_dvd
      m24_centralizerIn_comps e t ht).mono fun Y _ h => not_small_of_not_three h
  · change α ∈ inner NativeSporadic.M24
    rw [inner_eq_top_of_card_le m24_center_eq_bot' m24_mulAut_card]
    trivial

end CFSG.ComponentClassification.RestrictedStd.Spor
