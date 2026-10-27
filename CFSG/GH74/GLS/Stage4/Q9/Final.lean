module

public import CFSG.GH74.GLS.Stage4.Q9.Leaf
public import CFSG.GH74.GLS.Stage4.Q9.Main
public import CFSG.GH74.GLS.Stage4.Q9.ModelTheta

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open Subgroup

theorem q9_false
    {G : Type} [Group G] [Finite G] {z : G} {K₁ K₂ : Subgroup G} {F₁ F₂ : Type}
    [Field F₁] [Field F₂] (S : Q9Setting G z K₁ K₂ F₁ F₂) : False :=
  q9_false_of_model S model_theta_data model_counts

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Rest
  CFSG.Assembly.LowTwoRank in
theorem ch6t2bad9_of
    (hS : Q9SettingOf) : Ch6T2Bad9 := by
  intro G _ _ hStd hrank Gs _ hAt hBad
  obtain ⟨z, K₁, K₂, F₁, F₂, _, _, ⟨S⟩⟩ := hS G hStd hrank Gs hAt hBad
  exact q9_false S

end CFSG.GH74.GLS.Stage4.Q9
