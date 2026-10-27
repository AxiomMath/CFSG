module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRows

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (involutionCentralizersComponentFree_of_evenLieType)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def IsLinearUnitaryKind (κ : Sp2mKind) : Prop :=
  κ = .linearEven ∨ κ = .unitaryEven ∨ κ = .linearOdd ∨ κ = .unitaryOdd

theorem exists_lieModel_of_isLinearUnitaryKind {S : Type} [Group S] {m f : ℕ} {κ : Sp2mKind}
    (hκ : IsLinearUnitaryKind κ) (h : Sp2mKindType S m f κ) :
    ∃ (τ : StatedLieTag) (r : ℕ), (τ = .PSL ∨ τ = .PSU) ∧ (r = 2 * m ∨ r = 2 * m + 1) ∧
      LieModel S τ r 2 f := by
  rcases hκ with rfl | rfl | rfl | rfl
  · exact ⟨_, _, Or.inl rfl, Or.inl rfl, h⟩
  · exact ⟨_, _, Or.inr rfl, Or.inl rfl, h⟩
  · exact ⟨_, _, Or.inl rfl, Or.inr rfl, h⟩
  · exact ⟨_, _, Or.inr rfl, Or.inr rfl, h⟩

end CFSG.SeitzReduction.SymplecticPilot
