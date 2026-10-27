module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourLevi
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointSchreier

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.SeitzReduction.EPilot
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointSchreier
  (orthogonal_geometry_classical_model_Schreier)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem statedClassicalModel_of_lieModel_POmegaPlus_E7 {S : Type} [Group S] {n p f : ℕ}
    (h : LieModel S .POmegaPlus n p f) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel S .POmegaPlus n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

theorem statedClassicalModel_perpLevi_E7 {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel (perpLevi .E7 K) .POmegaPlus 6 2 f :=
  statedClassicalModel_of_lieModel_POmegaPlus_E7 (lieModel_perpLevi_E7 hK)

theorem exists_natCard_eq_two_pow_of_charP_two : ∃ f : ℕ, Nat.card K = 2 ^ f := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem isSolvable_outer_perpLevi_E7 : Group.IsSolvable (Outer (perpLevi .E7 K)) := by
  obtain ⟨f, hK⟩ := exists_natCard_eq_two_pow_of_charP_two (K := K)
  exact (orthogonal_geometry_classical_model_Schreier .POmegaPlus (Or.inr (Or.inl rfl))
    (statedClassicalModel_perpLevi_E7 hK)).2.2

end CFSG.SeitzReduction.E7Pilot
