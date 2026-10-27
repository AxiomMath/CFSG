module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderThree.InductionGram

public section

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical

variable {G : Type} [Group G]

theorem blocksIrr_finite (A : Type) [Group A] [Finite A] : (CFSG.BlocksIrr A).Finite := by
  let := Fintype.ofFinite A
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := A)
  rw [blocksIrr_eq_range_basis basis]
  exact Set.finite_range _

theorem character_restrict_sum_irreducible [Finite G] (S : Subgroup G) {V : Type}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    ∃ (size : ℕ) (θ : Fin size → S → ℂ), (∀ k, θ k ∈ CFSG.BlocksIrr S) ∧
      ∀ x : S, ρ.character x = ∑ k, θ k x := by
  let data : FiniteComplexRepresentation.{0, 0} S :=
    { vector := V, representation := ρ.comp S.subtype }
  obtain ⟨size, summand, hirr, hsum⟩ :=
    finiteComplexRepresentation_exists_irreducible_character_sum data
  refine ⟨size, fun k => (summand k).character, fun k => ?_, fun x => hsum x⟩
  rw [CFSG.blocksIrr_eq_irreducible_characters]
  exact ⟨summand k, hirr k, rfl⟩

theorem sylow_character_integer [Finite G] {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T))) {V : Type}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) {x : G}
    (hx : x ∈ (S : Subgroup G)) : ∃ k : ℤ, ρ.character x = k := by
  classical
  let := Fintype.ofFinite (S : Subgroup G)
  have hshape := unitaryFourSylowShape_of_mulEquiv hT S U hSU
  obtain ⟨-, -, -, -, -, -, -, -, hint, -⟩ := hshape.character_table
  obtain ⟨size, θ, hθ, hsum⟩ := character_restrict_sum_irreducible (S : Subgroup G) ρ
  choose k hk using fun j => hint (θ j) (hθ j) ⟨x, hx⟩
  refine ⟨∑ j, k j, ?_⟩
  rw [show x = ((⟨x, hx⟩ : (S : Subgroup G)) : G) from rfl, hsum, Int.cast_sum]
  exact Finset.sum_congr rfl fun j _ => hk j

end CFSG.LyonsUnitaryFour
