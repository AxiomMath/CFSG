module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviFactorExcInputs
public import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.Classify
public import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.DiagramF4
public import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.E8
public import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.F4
public import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.ModelMinuscule
public import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.TwistedE6
public import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.TwistedE6SU4
public import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.TwistedE6SU6
public import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.TwistedE6SpinMinus

public section

namespace CFSG.GroupTheory.GomiLeviExc

open Subgroup CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal CFSG.AGLEmbeddingD2.ParabLevi

private theorem ncard_lt_of_ne_univ {n : ℕ} {C : Set (Fin n)} (hne : C ≠ Set.univ) :
    C.ncard < n := by
  simpa using Set.ncard_lt_card hne

section F4

theorem gomiLeviFactorsF4_holds : GomiLeviFactorsF4 := by
  intro K _ _ _ C hC h2 hne
  rcases f4_connected_cases hC.2 h2 hne with rfl | rfl | rfl | rfl | rfl
  · exact F4.gomiLeviFactor_leviM_zero_one
  · exact F4.gomiLeviFactor_leviM_one_two
  · exact F4.gomiLeviFactor_leviM_two_three
  · exact F4.gomiLeviFactor_leviM_zero_one_two
  · exact F4.gomiLeviFactor_leviM_one_two_three

end F4

section E6

theorem gomiLeviFactorsE6_holds : GomiLeviFactorsE6 := by
  intro K _ _ _ C hC h2 hne
  have := CFSG.LieType.Steinberg.CentralExt.FieldFour.finite_minGroup' (K := K) e6Data_valid
  have hlt : C.ncard < 6 := ncard_lt_of_ne_univ hne
  refine gomiLeviFactor_leviM_of_isSymm (e6Datum_isCTGroupDatum K) rfl
    (e6Datum_isParametrization K _ (roots_eq isFiniteType_cartan_E6)) ?_
    (MinusculeModel.isCharTwoSteinberg_e6 K) (fun t ht hsl hr => ?_) hC h2
  · change (Tag.cartan .E6).IsSymm
    rw [cartan_E6]
    exact CartanMatrix.E_isSymm 6
  · refine hasCharTwoModel_of_isSimplyLaced K (fun _ _ => isChevTwo_psl K (Or.inl (by omega)))
      ht hsl (by omega) ?_ ?_ ?_
    · rintro rfl
      rw [TauCeti.DynkinType.rank_E6] at hr
      omega
    · rintro rfl
      rw [TauCeti.DynkinType.rank_E7] at hr
      omega
    · rintro rfl
      rw [TauCeti.DynkinType.rank_E8] at hr
      omega

end E6

section E7

theorem gomiLeviFactorsE7_holds : GomiLeviFactorsE7 := by
  intro K _ _ _ C hC h2 hne
  have := CFSG.LieType.Steinberg.CentralExt.FieldFour.finite_minGroup' (K := K) e7Data_valid
  have hlt : C.ncard < 7 := ncard_lt_of_ne_univ hne
  refine gomiLeviFactor_leviM_of_isSymm (e7Datum_isCTGroupDatum K) rfl
    (e7Datum_isParametrization K _ (roots_eq isFiniteType_cartan_E7)) ?_
    (MinusculeModel.isCharTwoSteinberg_e7 K) (fun t ht hsl hr => ?_) hC h2
  · change (Tag.cartan .E7).IsSymm
    rw [cartan_E7]
    exact CartanMatrix.E_isSymm 7
  · refine hasCharTwoModel_of_isSimplyLaced K (fun _ _ => isChevTwo_psl K (Or.inl (by omega)))
      ht hsl (by omega)
      (fun _ => MinusculeModel.hasCharTwoModel_E6 K) ?_ ?_
    · rintro rfl
      rw [TauCeti.DynkinType.rank_E7] at hr
      omega
    · rintro rfl
      rw [TauCeti.DynkinType.rank_E8] at hr
      omega

end E7

section E8

theorem gomiLeviFactorsE8_holds : GomiLeviFactorsE8 := by
  intro K _ _ _ C hC h2 hne
  have : Finite ↥(adjointGroup .E8 K) := CFSG.LieType.Chevalley.generated_group_finite .E8 K
  have hlt : C.ncard < 8 := ncard_lt_of_ne_univ hne
  refine gomiLeviFactor_leviM_of_isSymm (e8_isCTGroupDatum K) rfl (e8_isParametrization K) ?_
    (E8.isCharTwoSteinberg K) (fun t ht hsl hr => ?_) hC h2
  · change (Tag.cartanE 8).IsSymm
    rw [CFSG.LieType.Chevalley.cartanE_eq]
    exact CartanMatrix.E_isSymm 8
  · refine hasCharTwoModel_of_isSimplyLaced K (fun _ _ => isChevTwo_psl K (Or.inl (by omega)))
      ht hsl (by omega)
      (fun _ => MinusculeModel.hasCharTwoModel_E6 K) (fun _ => MinusculeModel.hasCharTwoModel_E7 K)
      ?_
    rintro rfl
    rw [TauCeti.DynkinType.rank_E8] at hr
    omega

end E8

section TwistedE6

theorem gomiLeviFactorsTwistedE6_holds : GomiLeviFactorsTwistedE6 := by
  intro k _ _ _ θ q hk hθ C hC h2 hne
  rcases f4_connected_cases hC.2 h2 hne with rfl | rfl | rfl | rfl | rfl
  · exact TwistedE6.gomiLeviFactor_leviM_zero_one
  · exact TwistedE6.gomiLeviFactor_leviM_one_two hk hθ
  · exact TwistedE6.gomiLeviFactor_leviM_two_three hk hθ
  · exact TwistedE6.gomiLeviFactor_leviM_zero_one_two hk hθ
  · exact TwistedE6.gomiLeviFactor_leviM_one_two_three hk hθ

end TwistedE6

end CFSG.GroupTheory.GomiLeviExc
