module

public import CFSG.GH74.GLS.Classes
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
public import CFSG.LocalAnalysis.StandardType.ChevTwoMarking
public import CFSG.Adapters.StatedPSLTwoSeven
public import CFSG.Adapters.StatedPSLTwoNine

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.SporChev2

open CFSG Blueprint Assembly.LowTwoRank

theorem statedClassicalModel_of_lieModel_psl {X : Type} [Group X] {n p f : ℕ}
    (h : LieModel X .PSL n p f) : StatedClassicalModel X .PSL n p f :=
  h.statedClassicalModel (by decide)

theorem inChev2_of_lieModel_psl_two_five {X : Type} [Group X]
    (h : LieModel X .PSL 2 5 1) : GH74.GLS.InChev2 X := by
  obtain ⟨e⟩ := QuasithinUnique.Setup.Family.alternating_five_of_model_five
    (statedClassicalModel_of_lieModel_psl h)
  exact Or.inl ⟨.PSL, 2, 2, ⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩,
    StandardType.ChevTwo.lieModel_psl_two_four_of_alternating_five e⟩

theorem inChev2_of_lieModel_psl_two_seven {X : Type} [Group X] (h : LieModel X .PSL 2 7 1) :
    GH74.GLS.InChev2 X := by
  have hc := Open.StatedAPI.statedClassicalModel_psl_three_two_of_psl_two_seven
    (statedClassicalModel_of_lieModel_psl h)
  exact Or.inl ⟨.PSL, 3, 1, hc.1, Or.inl ⟨by decide, hc⟩⟩

theorem inChev2_of_lieModel_psl_two_nine {X : Type} [Group X] (h : LieModel X .PSL 2 3 2) :
    GH74.GLS.InChev2 X :=
  Or.inr (Or.inl h.nonempty_mulEquiv_alternating_six)

variable {X : Type} [Group X] {τ : StatedLieTag} {n p f : ℕ}

theorem inChev2_of_tuple_five (hL : LieModel X τ n p f)
    (ht : (τ, n, p, f) = (.PSL, 2, 5, 1)) : GH74.GLS.InChev2 X := by
  simp only [Prod.mk.injEq] at ht
  obtain ⟨rfl, rfl, rfl, rfl⟩ := ht
  exact inChev2_of_lieModel_psl_two_five hL

theorem inChev2_of_tuple_seven (hL : LieModel X τ n p f) (ht : (τ, n, p, f) = (.PSL, 2, 7, 1)) :
    GH74.GLS.InChev2 X := by
  simp only [Prod.mk.injEq] at ht
  obtain ⟨rfl, rfl, rfl, rfl⟩ := ht
  exact inChev2_of_lieModel_psl_two_seven hL

theorem inChev2_of_tuple_nine (hL : LieModel X τ n p f) (ht : (τ, n, p, f) = (.PSL, 2, 3, 2)) :
    GH74.GLS.InChev2 X := by
  simp only [Prod.mk.injEq] at ht
  obtain ⟨rfl, rfl, rfl, rfl⟩ := ht
  exact inChev2_of_lieModel_psl_two_nine hL

end CFSG.ComponentClassification.GS82PumpInputs.SporChev2
