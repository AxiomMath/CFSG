module

public import CFSG.GH74.Orders.LieType
import CFSG.Blueprint.LieModelAPI
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.Filter.ClassicalOdd.Symplectic
public import CFSG.GH74.Filter.ClassicalOdd.Unitary
public import CFSG.GH74.Filter.Lie.EvenSeries
public import CFSG.GH74.Filter.Lie.Suzuki
public import CFSG.GH74.Filter.Lie.TitsElem
public import CFSG.GH74.Filter.Lie.TwistedD4Even
public import CFSG.GH74.Filter.Lie.TwistedE6Even
public import CFSG.GH74.Filter.Lie.TwistedE6Odd
public import CFSG.GH74.Filter.Lie.TwistedF4
public import CFSG.GH74.Filter.Orthogonal.EvenEichler
public import CFSG.GH74.Filter.Orthogonal.OddReflections
public import CFSG.GH74.Filter.Orthogonal.UnitaryEven
public import CFSG.GH74.Filter.Small.Exceptional
public import CFSG.GH74.Filter.Small.Unipotent
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Generic.S3.L3Ord

open CFSG CFSG.GH74 CFSG.GH74.Filter CFSG.Blueprint CFSG.Assembly.LowTwoRank

section Clauses

variable {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}

theorem classical_clause (ht : t ∈ classicalTags) (h : LieModel X t n p f) :
    StatedClassicalModel X t n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h ht

theorem reeTits_clause (ht : t ∈ reeTitsTags) (h : LieModel X t n p f) : ReeTitsModel X t p f :=
  (CFSG.Blueprint.LieModel.reeTitsModel h ht).2

theorem suzuki_clause (h : LieModel X .twistedB2 n p f) : SuzukiModel X p f :=
  (CFSG.Blueprint.LieModel.suzukiModel h).2

end Clauses

theorem gen4Model_of_lieModel
    {X : Type} [Group X] [Finite X] (hX : Gen4 X) {t : StatedLieTag} {n p f : ℕ}
    (h : LieModel X t n p f) :
    match t with
    | .PSL => n ≤ 5
    | .PSU => (n ≤ 5 ∧ p ≠ 2) ∨ (p = 2 ∧ f * (n - 2) ≤ 2)
    | .PSp => (n = 2 ∧ p ≠ 2) ∨ (p = 2 ∧ f * (n + 1) ≤ 4)
    | .G2 => p ≠ 2
    | .trialityD4 => p ≠ 2
    | .twistedG2 => True
    | .twistedB2 => f ≤ 4
    | _ => False := by
  cases t
  ·
    have hs : StatedClassicalModel X .PSL n p f := classical_clause (by decide) h
    obtain ⟨hp, hf, hn2, -, -⟩ := hs.1
    show n ≤ 5
    by_contra hn
    have hn6 : 6 ≤ n := by omega
    by_cases hp2 : p = 2
    · subst hp2
      exact t_PSL_even_unipotent X n f hs (unip_PSL_bound hn6 hf) hX
    · by_cases h6 : n = 6
      · subst h6
        exact t_PSL_six_odd X p f hp2 hs hX
      · exact t_PSL_ge_seven_odd X n p f hp2 (by omega) hs hX
  ·
    have hs : StatedClassicalModel X .PSU n p f := classical_clause (by decide) h
    obtain ⟨hp, hf, hn3, -⟩ := hs.1
    show (n ≤ 5 ∧ p ≠ 2) ∨ (p = 2 ∧ f * (n - 2) ≤ 2)
    by_cases hp2 : p = 2
    · subst hp2
      right
      refine ⟨rfl, ?_⟩
      by_contra hc
      exact t_PSU_even X n f hs (by omega) hX
    · left
      refine ⟨?_, hp2⟩
      by_contra hn
      by_cases h6 : n = 6
      · subst h6
        exact t_PSU_six_odd X p f hp2 hs hX
      · exact t_PSU_ge_seven_odd X n p f hp2 (by omega) hs hX
  ·
    have hs : StatedClassicalModel X .PSp n p f := classical_clause (by decide) h
    obtain ⟨hp, hf, hn2, -⟩ := hs.1
    show (n = 2 ∧ p ≠ 2) ∨ (p = 2 ∧ f * (n + 1) ≤ 4)
    by_cases hp2 : p = 2
    · subst hp2
      right
      refine ⟨rfl, ?_⟩
      by_contra hc
      exact t_PSp_even_unipotent X n f hs (by omega) hX
    · left
      refine ⟨?_, hp2⟩
      by_contra hn
      exact t_PSp_odd_ge_three X n p f hp2 (by omega) hs hX
  ·
    have hs : StatedClassicalModel X .POmegaOdd n p f := classical_clause (by decide) h
    obtain ⟨hp, hf, hn3, hp2⟩ := hs.1
    exact (t_POmegaOdd X n p f hp2 hn3 hs hX).elim
  ·
    have hs : StatedClassicalModel X .POmegaPlus n p f := classical_clause (by decide) h
    by_cases hp2 : p = 2
    · subst hp2
      exact (t_POmegaPlus_even X n f hs hX).elim
    · exact (t_POmegaPlus_odd X n p f hp2 hs hX).elim
  ·
    have hs : StatedClassicalModel X .POmegaMinus n p f := classical_clause (by decide) h
    by_cases hp2 : p = 2
    · subst hp2
      exact (t_POmegaMinus_even X n f hs hX).elim
    · exact (t_POmegaMinus_odd X n p f hp2 hs hX).elim
  ·
    have hm := chevalleyExceptionalModel_of_lieModel (by decide) h
    show p ≠ 2
    rintro rfl
    exact t_G2_even X f hm hX
  ·
    have hm := chevalleyExceptionalModel_of_lieModel (by decide) h
    by_cases hp2 : p = 2
    · subst hp2
      exact (t_F4_even X f hm hX).elim
    · exact (t_F4_odd X p f hp2 hm hX).elim
  ·
    have hm := chevalleyExceptionalModel_of_lieModel (by decide) h
    by_cases hp2 : p = 2
    · subst hp2
      exact (t_E6_even X f hm hX).elim
    · exact (t_E6_odd X p f hp2 hm hX).elim
  ·
    have hm := chevalleyExceptionalModel_of_lieModel (by decide) h
    by_cases hp2 : p = 2
    · subst hp2
      exact (t_E7_even X f hm hX).elim
    · exact (t_E7_odd X p f hp2 hm hX).elim
  ·
    have hm := chevalleyExceptionalModel_of_lieModel (by decide) h
    by_cases hp2 : p = 2
    · subst hp2
      exact (t_E8_even X f hm hX).elim
    · exact (t_E8_odd X p f hp2 hm hX).elim
  ·
    have hm := chevalleyExceptionalModel_of_lieModel (by decide) h
    by_cases hp2 : p = 2
    · subst hp2
      exact (t_2E6_even X f hm hX).elim
    · exact (t_2E6_odd X p f hp2 hm hX).elim
  ·
    have hm := chevalleyExceptionalModel_of_lieModel (by decide) h
    show p ≠ 2
    rintro rfl
    exact t_3D4_even X f hm hX
  ·
    have hS := suzuki_clause h
    show f ≤ 4
    by_contra hf
    exact t_suzuki_large X p f (by omega) hS hX
  ·
    trivial
  ·
    have hm := reeTits_clause (by decide) h
    have hadm := hm.1
    obtain ⟨-, -, -, hp2, -⟩ := hadm
    subst hp2
    exact (t_twistedF4 X f hm hX).elim
  ·
    have hm := reeTits_clause (by decide) h
    have hadm := hm.1
    obtain ⟨-, -, -, hp2, hf1⟩ := hadm
    subst hp2
    subst hf1
    exact (t_Tits X hm hX).elim

end CFSG.GH74.Generic.S3.L3Ord
