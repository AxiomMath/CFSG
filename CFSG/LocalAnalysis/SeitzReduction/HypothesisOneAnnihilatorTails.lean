module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneAnnihilator

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K]

@[expose] def annihS_E6_four : List (Fin Tag.E6.rank → ℤ) :=
  [![0, 1, 0, 1, 1, 1],
    ![0, 1, 1, 1, 1, 0],
    ![1, 0, 1, 1, 1, 0],
    ![1, 1, 1, 1, 0, 0],
    ![1, 0, 1, 1, 1, 1]]

@[expose] def annihL_E6_four : List (Fin Tag.E6.rank → ℤ) :=
  [![1, 1, 1, 1, 0, 0],
    ![1, 1, 1, 1, 1, 0],
    ![1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 2, 1, 0],
    ![1, 1, 1, 2, 2, 1],
    ![1, 1, 2, 2, 1, 1],
    ![1, 1, 2, 2, 2, 1],
    ![1, 1, 2, 3, 2, 1],
    ![1, 2, 2, 3, 2, 1]]

theorem annListCheck_E6_four :
    annListCheck .E6 11 annihS_E6_four annihL_E6_four = true := by
  decide +kernel

theorem le_height_annihS_E6_four : ∀ δ ∈ annihS_E6_four, (4 : ℤ) ≤ height δ := by
  decide +kernel

@[expose] def annihS_E6_five : List (Fin Tag.E6.rank → ℤ) :=
  [![1, 0, 1, 1, 1, 1],
    ![0, 1, 1, 2, 1, 1],
    ![1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 2, 1, 0],
    ![0, 1, 1, 2, 2, 1],
    ![1, 1, 2, 2, 1, 0]]

@[expose] def annihL_E6_five : List (Fin Tag.E6.rank → ℤ) :=
  [![1, 0, 1, 1, 1, 1],
    ![0, 1, 1, 2, 1, 1],
    ![1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 2, 1, 0],
    ![0, 1, 1, 2, 2, 1],
    ![1, 1, 1, 2, 1, 1],
    ![1, 1, 2, 2, 1, 0],
    ![1, 1, 1, 2, 2, 1],
    ![1, 1, 2, 2, 1, 1],
    ![1, 1, 2, 2, 2, 1],
    ![1, 1, 2, 3, 2, 1],
    ![1, 2, 2, 3, 2, 1]]

theorem annListCheck_E6_five :
    annListCheck .E6 11 annihS_E6_five annihL_E6_five = true := by
  decide +kernel

theorem le_height_annihS_E6_five : ∀ δ ∈ annihS_E6_five, (5 : ℤ) ≤ height δ := by
  decide +kernel

@[expose] def annihS_E7_five : List (Fin Tag.E7.rank → ℤ) :=
  [![0, 0, 1, 1, 1, 1, 1],
    ![0, 1, 0, 1, 1, 1, 1],
    ![0, 1, 1, 1, 1, 1, 0],
    ![0, 1, 1, 2, 1, 0, 0],
    ![1, 1, 1, 1, 1, 0, 0],
    ![0, 1, 1, 2, 1, 1, 0],
    ![1, 0, 1, 1, 1, 1, 1]]

@[expose] def annihL_E7_five : List (Fin Tag.E7.rank → ℤ) :=
  [![0, 1, 0, 1, 1, 1, 1],
    ![0, 1, 1, 1, 1, 1, 1],
    ![0, 1, 1, 2, 2, 1, 1],
    ![1, 1, 2, 2, 1, 1, 1],
    ![1, 2, 2, 3, 2, 1, 1],
    ![1, 1, 2, 3, 3, 2, 1],
    ![1, 2, 2, 3, 2, 2, 1],
    ![1, 2, 2, 3, 3, 2, 1],
    ![1, 2, 2, 4, 3, 2, 1],
    ![1, 2, 3, 4, 3, 2, 1],
    ![2, 2, 3, 4, 3, 2, 1]]

theorem annListCheck_E7_five :
    annListCheck .E7 17 annihS_E7_five annihL_E7_five = true := by
  decide +kernel

theorem le_height_annihS_E7_five : ∀ δ ∈ annihS_E7_five, (5 : ℤ) ≤ height δ := by
  decide +kernel

@[expose] def annihS_E7_seven : List (Fin Tag.E7.rank → ℤ) :=
  [![0, 1, 1, 2, 1, 1, 1],
    ![0, 1, 1, 2, 2, 1, 0],
    ![1, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 2, 1, 1, 0],
    ![1, 1, 2, 2, 1, 0, 0],
    ![1, 1, 1, 2, 1, 1, 1],
    ![1, 1, 1, 2, 2, 1, 0],
    ![1, 1, 2, 2, 1, 1, 0],
    ![0, 1, 1, 2, 2, 2, 1],
    ![1, 1, 2, 2, 2, 1, 0],
    ![1, 1, 2, 3, 2, 1, 0]]

@[expose] def annihL_E7_seven : List (Fin Tag.E7.rank → ℤ) :=
  [![1, 1, 1, 2, 1, 1, 0],
    ![1, 1, 2, 2, 1, 1, 0],
    ![1, 1, 2, 2, 2, 2, 1],
    ![1, 1, 2, 3, 2, 1, 1],
    ![1, 2, 2, 3, 2, 1, 0],
    ![1, 1, 2, 3, 2, 2, 1],
    ![1, 2, 2, 3, 2, 1, 1],
    ![1, 1, 2, 3, 3, 2, 1],
    ![1, 2, 2, 3, 2, 2, 1],
    ![1, 2, 2, 3, 3, 2, 1],
    ![1, 2, 2, 4, 3, 2, 1],
    ![1, 2, 3, 4, 3, 2, 1],
    ![2, 2, 3, 4, 3, 2, 1]]

theorem annListCheck_E7_seven :
    annListCheck .E7 17 annihS_E7_seven annihL_E7_seven = true := by
  decide +kernel

theorem le_height_annihS_E7_seven : ∀ δ ∈ annihS_E7_seven, (7 : ℤ) ≤ height δ := by
  decide +kernel

@[expose] def annihS_E7_nine : List (Fin Tag.E7.rank → ℤ) :=
  [![0, 1, 1, 2, 2, 2, 1],
    ![1, 1, 1, 2, 2, 1, 1],
    ![1, 1, 2, 2, 1, 1, 1],
    ![1, 1, 2, 2, 2, 1, 0],
    ![1, 1, 1, 2, 2, 2, 1],
    ![1, 1, 2, 2, 2, 1, 1],
    ![1, 1, 2, 3, 2, 1, 0],
    ![1, 1, 2, 3, 2, 1, 1],
    ![1, 2, 2, 3, 2, 1, 0],
    ![1, 2, 2, 3, 2, 1, 1]]

@[expose] def annihL_E7_nine : List (Fin Tag.E7.rank → ℤ) :=
  [![0, 1, 1, 2, 2, 1, 1],
    ![0, 1, 1, 2, 2, 2, 1],
    ![1, 1, 1, 2, 2, 1, 1],
    ![1, 1, 2, 2, 1, 1, 1],
    ![1, 1, 2, 2, 2, 1, 0],
    ![1, 1, 1, 2, 2, 2, 1],
    ![1, 1, 2, 2, 2, 1, 1],
    ![1, 1, 2, 3, 2, 1, 0],
    ![1, 1, 2, 2, 2, 2, 1],
    ![1, 1, 2, 3, 2, 1, 1],
    ![1, 2, 2, 3, 2, 1, 0],
    ![1, 1, 2, 3, 2, 2, 1],
    ![1, 2, 2, 3, 2, 1, 1],
    ![1, 1, 2, 3, 3, 2, 1],
    ![1, 2, 2, 3, 2, 2, 1],
    ![1, 2, 2, 3, 3, 2, 1],
    ![1, 2, 2, 4, 3, 2, 1],
    ![1, 2, 3, 4, 3, 2, 1],
    ![2, 2, 3, 4, 3, 2, 1]]

theorem annListCheck_E7_nine :
    annListCheck .E7 17 annihS_E7_nine annihL_E7_nine = true := by
  decide +kernel

theorem le_height_annihS_E7_nine : ∀ δ ∈ annihS_E7_nine, (9 : ℤ) ≤ height δ := by
  decide +kernel

@[expose] def annihS_E8_seven : List (Fin Tag.E8.rank → ℤ) :=
  [![0, 1, 1, 1, 1, 1, 1, 1],
    ![0, 1, 1, 2, 2, 1, 0, 0],
    ![1, 0, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1, 0],
    ![1, 1, 1, 2, 1, 1, 0, 0],
    ![1, 1, 2, 2, 1, 0, 0, 0],
    ![0, 1, 1, 2, 1, 1, 1, 1],
    ![1, 1, 2, 2, 1, 1, 0, 0]]

@[expose] def annihL_E8_seven : List (Fin Tag.E8.rank → ℤ) :=
  [![1, 1, 2, 2, 1, 0, 0, 0],
    ![1, 1, 2, 2, 1, 1, 0, 0],
    ![1, 1, 2, 2, 2, 2, 1, 1],
    ![1, 2, 2, 3, 2, 1, 1, 1],
    ![1, 2, 2, 3, 2, 2, 1, 1],
    ![1, 2, 2, 3, 3, 2, 1, 1],
    ![2, 2, 3, 4, 3, 2, 1, 1],
    ![1, 2, 3, 4, 3, 3, 2, 1],
    ![2, 2, 4, 5, 4, 3, 2, 1],
    ![2, 3, 3, 5, 4, 3, 2, 1],
    ![2, 3, 4, 5, 4, 3, 2, 1],
    ![2, 3, 4, 6, 4, 3, 2, 1],
    ![2, 3, 4, 6, 5, 3, 2, 1],
    ![2, 3, 4, 6, 5, 4, 2, 1],
    ![2, 3, 4, 6, 5, 4, 3, 1],
    ![2, 3, 4, 6, 5, 4, 3, 2]]

theorem annListCheck_E8_seven :
    annListCheck .E8 29 annihS_E8_seven annihL_E8_seven = true := by
  decide +kernel

theorem le_height_annihS_E8_seven : ∀ δ ∈ annihS_E8_seven, (7 : ℤ) ≤ height δ := by
  decide +kernel

@[expose] def annihS_E8_eleven : List (Fin Tag.E8.rank → ℤ) :=
  [![0, 1, 1, 2, 2, 2, 2, 1],
    ![1, 1, 1, 2, 2, 2, 1, 1],
    ![1, 1, 2, 2, 2, 1, 1, 1],
    ![1, 1, 2, 3, 2, 1, 1, 0],
    ![1, 2, 2, 3, 2, 1, 0, 0],
    ![1, 1, 1, 2, 2, 2, 2, 1],
    ![1, 1, 2, 2, 2, 2, 1, 1],
    ![1, 1, 2, 3, 2, 1, 1, 1],
    ![1, 1, 2, 3, 2, 2, 1, 0],
    ![1, 1, 2, 3, 3, 2, 1, 0]]

@[expose] def annihL_E8_eleven : List (Fin Tag.E8.rank → ℤ) :=
  [![1, 1, 2, 3, 2, 1, 1, 1],
    ![1, 1, 2, 3, 2, 2, 1, 1],
    ![1, 1, 2, 3, 3, 2, 1, 0],
    ![1, 1, 2, 3, 3, 2, 1, 1],
    ![1, 2, 2, 4, 3, 2, 1, 1],
    ![1, 2, 2, 4, 4, 3, 2, 1],
    ![1, 2, 3, 4, 3, 3, 2, 1],
    ![2, 2, 3, 4, 3, 2, 2, 1],
    ![1, 2, 3, 4, 4, 3, 2, 1],
    ![2, 2, 3, 4, 3, 3, 2, 1],
    ![1, 2, 3, 5, 4, 3, 2, 1],
    ![2, 2, 3, 4, 4, 3, 2, 1],
    ![1, 3, 3, 5, 4, 3, 2, 1],
    ![2, 2, 3, 5, 4, 3, 2, 1],
    ![2, 2, 4, 5, 4, 3, 2, 1],
    ![2, 3, 3, 5, 4, 3, 2, 1],
    ![2, 3, 4, 5, 4, 3, 2, 1],
    ![2, 3, 4, 6, 4, 3, 2, 1],
    ![2, 3, 4, 6, 5, 3, 2, 1],
    ![2, 3, 4, 6, 5, 4, 2, 1],
    ![2, 3, 4, 6, 5, 4, 3, 1],
    ![2, 3, 4, 6, 5, 4, 3, 2]]

theorem annListCheck_E8_eleven :
    annListCheck .E8 29 annihS_E8_eleven annihL_E8_eleven = true := by
  decide +kernel

theorem le_height_annihS_E8_eleven : ∀ δ ∈ annihS_E8_eleven, (11 : ℤ) ≤ height δ := by
  decide +kernel

@[expose] def annihS_E8_thirteen : List (Fin Tag.E8.rank → ℤ) :=
  [![1, 1, 2, 2, 2, 2, 2, 1],
    ![1, 2, 2, 3, 2, 1, 1, 1],
    ![1, 1, 2, 3, 2, 2, 2, 1],
    ![1, 1, 2, 3, 3, 2, 1, 1],
    ![1, 2, 2, 3, 2, 2, 1, 1],
    ![1, 2, 2, 3, 3, 2, 1, 0],
    ![1, 1, 2, 3, 3, 2, 2, 1],
    ![1, 2, 2, 4, 3, 2, 1, 0],
    ![1, 1, 2, 3, 3, 3, 2, 1],
    ![1, 2, 3, 4, 3, 2, 1, 0],
    ![2, 2, 3, 4, 3, 2, 1, 0]]

@[expose] def annihL_E8_thirteen : List (Fin Tag.E8.rank → ℤ) :=
  [![1, 1, 2, 3, 3, 2, 1, 1],
    ![1, 2, 2, 3, 3, 2, 2, 1],
    ![1, 2, 3, 4, 3, 2, 1, 0],
    ![1, 2, 2, 3, 3, 3, 2, 1],
    ![1, 2, 2, 4, 3, 2, 2, 1],
    ![1, 2, 3, 4, 3, 2, 1, 1],
    ![2, 2, 3, 4, 3, 2, 1, 0],
    ![1, 2, 2, 4, 3, 3, 2, 1],
    ![1, 2, 3, 4, 3, 2, 2, 1],
    ![2, 2, 3, 4, 3, 2, 1, 1],
    ![1, 2, 2, 4, 4, 3, 2, 1],
    ![1, 2, 3, 4, 3, 3, 2, 1],
    ![2, 2, 3, 4, 3, 2, 2, 1],
    ![1, 2, 3, 4, 4, 3, 2, 1],
    ![2, 2, 3, 4, 3, 3, 2, 1],
    ![1, 2, 3, 5, 4, 3, 2, 1],
    ![2, 2, 3, 4, 4, 3, 2, 1],
    ![1, 3, 3, 5, 4, 3, 2, 1],
    ![2, 2, 3, 5, 4, 3, 2, 1],
    ![2, 2, 4, 5, 4, 3, 2, 1],
    ![2, 3, 3, 5, 4, 3, 2, 1],
    ![2, 3, 4, 5, 4, 3, 2, 1],
    ![2, 3, 4, 6, 4, 3, 2, 1],
    ![2, 3, 4, 6, 5, 3, 2, 1],
    ![2, 3, 4, 6, 5, 4, 2, 1],
    ![2, 3, 4, 6, 5, 4, 3, 1],
    ![2, 3, 4, 6, 5, 4, 3, 2]]

theorem annListCheck_E8_thirteen :
    annListCheck .E8 29 annihS_E8_thirteen annihL_E8_thirteen = true := by
  decide +kernel

theorem le_height_annihS_E8_thirteen : ∀ δ ∈ annihS_E8_thirteen, (13 : ℤ) ≤ height δ := by
  decide +kernel


theorem sq_eq_one_of_commute_heightSeries_E6_four [CharP K 2] {u : ModGL .E6 K}
    (hu : u ∈ posUnipotent .E6 K) (hc : ∀ x ∈ heightSeries .E6 K 4, u * x = x * u) :
    u ^ 2 = 1 :=
  sq_eq_one_of_commute_heightSeries_of_annListCheck (Or.inr (Or.inl rfl))
    annListCheck_E6_four le_height_annihS_E6_four hu hc

theorem sq_eq_one_of_commute_heightSeries_E6_five [CharP K 2] {u : ModGL .E6 K}
    (hu : u ∈ posUnipotent .E6 K) (hc : ∀ x ∈ heightSeries .E6 K 5, u * x = x * u) :
    u ^ 2 = 1 :=
  sq_eq_one_of_commute_heightSeries_of_annListCheck (Or.inr (Or.inl rfl))
    annListCheck_E6_five le_height_annihS_E6_five hu hc

theorem sq_eq_one_of_commute_heightSeries_E7_five [CharP K 2] {u : ModGL .E7 K}
    (hu : u ∈ posUnipotent .E7 K) (hc : ∀ x ∈ heightSeries .E7 K 5, u * x = x * u) :
    u ^ 2 = 1 :=
  sq_eq_one_of_commute_heightSeries_of_annListCheck (Or.inr (Or.inr (Or.inl rfl)))
    annListCheck_E7_five le_height_annihS_E7_five hu hc

theorem sq_eq_one_of_commute_heightSeries_E7_seven [CharP K 2] {u : ModGL .E7 K}
    (hu : u ∈ posUnipotent .E7 K) (hc : ∀ x ∈ heightSeries .E7 K 7, u * x = x * u) :
    u ^ 2 = 1 :=
  sq_eq_one_of_commute_heightSeries_of_annListCheck (Or.inr (Or.inr (Or.inl rfl)))
    annListCheck_E7_seven le_height_annihS_E7_seven hu hc

theorem sq_eq_one_of_commute_heightSeries_E7_nine [CharP K 2] {u : ModGL .E7 K}
    (hu : u ∈ posUnipotent .E7 K) (hc : ∀ x ∈ heightSeries .E7 K 9, u * x = x * u) :
    u ^ 2 = 1 :=
  sq_eq_one_of_commute_heightSeries_of_annListCheck (Or.inr (Or.inr (Or.inl rfl)))
    annListCheck_E7_nine le_height_annihS_E7_nine hu hc

theorem sq_eq_one_of_commute_heightSeries_E8_seven [CharP K 2] {u : ModGL .E8 K}
    (hu : u ∈ posUnipotent .E8 K) (hc : ∀ x ∈ heightSeries .E8 K 7, u * x = x * u) :
    u ^ 2 = 1 :=
  sq_eq_one_of_commute_heightSeries_of_annListCheck (Or.inr (Or.inr (Or.inr rfl)))
    annListCheck_E8_seven le_height_annihS_E8_seven hu hc

theorem sq_eq_one_of_commute_heightSeries_E8_eleven [CharP K 2] {u : ModGL .E8 K}
    (hu : u ∈ posUnipotent .E8 K) (hc : ∀ x ∈ heightSeries .E8 K 11, u * x = x * u) :
    u ^ 2 = 1 :=
  sq_eq_one_of_commute_heightSeries_of_annListCheck (Or.inr (Or.inr (Or.inr rfl)))
    annListCheck_E8_eleven le_height_annihS_E8_eleven hu hc

theorem sq_eq_one_of_commute_heightSeries_E8_thirteen [CharP K 2] {u : ModGL .E8 K}
    (hu : u ∈ posUnipotent .E8 K) (hc : ∀ x ∈ heightSeries .E8 K 13, u * x = x * u) :
    u ^ 2 = 1 :=
  sq_eq_one_of_commute_heightSeries_of_annListCheck (Or.inr (Or.inr (Or.inr rfl)))
    annListCheck_E8_thirteen le_height_annihS_E8_thirteen hu hc

end CFSG.SeitzReduction
