module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69Full.Struct
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69Full.ShapeCard
public import CFSG.Quasithin.Background.B69Main

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B69

variable {V : Type} [CommGroup V] [Finite V]

theorem not_isStrongFFModule_K (hP4 : AsB15Part4) (hComp : AsB69ComponentK) (hV : ∀ v : V, v ^ 2 = 1)
    {X T M : Subgroup (MulAut V)} (hK : CFSG.SectionRank.IsKGroupCat ↥X) (h : MinParabolic X T M)
    (hO2 : pCoreOf 2 X = ⊥) (hFF : IsFFModule X) : ¬ IsStrongFFModule X := by
  intro hstrong
  by_cases hsolv : Group.IsSolvable ↥X
  · exact not_isStrongFFModule_of_isSolvable hV hsolv hO2 hstrong
  · obtain ⟨A, hA, hAs⟩ := exists_strong_pstar hV hstrong
    have hFA := strong_centralizes_fitting hV hO2 hA hAs
    obtain ⟨L, hL, hLA⟩ := exists_component hV hP4 hO2 hA hFA
    obtain ⟨W, hW⟩ := exists_irrPlus hL.2.2
    have hshape : CompShape T M A L W :=
      asB69ComponentK_iff.1 hComp V hV X T M A L ⟨hK, h, hO2, hFF, hsolv, hA, hL, hLA⟩ W hW
    exact not_rAV_lt_one_of_shape hV hA hL.2.2 hLA hW hshape hAs

theorem qOf_eq_one_K (hP4 : AsB15Part4) (hComp : AsB69ComponentK) (hV : ∀ v : V, v ^ 2 = 1)
    {X T M : Subgroup (MulAut V)} (hK : CFSG.SectionRank.IsKGroupCat ↥X) (h : MinParabolic X T M)
    (hO2 : pCoreOf 2 X = ⊥) (hFF : IsFFModule X) :
    qOf X = 1 ∧ ∀ A, ¬ IsStrongFFStarOffender X A := by
  have hns : ¬ IsStrongFFModule X := not_isStrongFFModule_K hP4 hComp hV hK h hO2 hFF
  refine ⟨?_, fun A hA => hns ?_⟩
  · have h1 : qOf X ≤ 1 := ((B1_4_5 hV X).out 1 3).1 hFF
    have h2 : (1 : WithTop ℚ) ≤ qOf X := by
      have h3 : ((1 : ℚ) : WithTop ℚ) ≤ qOf X := by
        unfold qOf
        refine le_kq_iff.2 fun A hA2 _ => ?_
        by_contra hlt
        push Not at hlt
        exact hns ⟨A, hA2.1, hA2.2.1, hA2.2.2, (rAV_lt_one_iff hV hA2).1 hlt⟩
      simpa using h3
    exact le_antisymm h1 h2
  · exact ⟨A, hA.1.1, hA.1.2.1, hA.1.2.2.1, (rAV_lt_one_iff hV hA.1.isA2).1 hA.2⟩

end B69

end CFSG.Quasithin
