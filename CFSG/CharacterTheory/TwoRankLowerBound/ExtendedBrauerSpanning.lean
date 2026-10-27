module

public import CFSG.CharacterTheory.TwoRankLowerBound.ElementaryDeltaWitness

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem elementaryInductionIdeal_not_le_maximal {G : Type*} [Group G] [Fintype G]
    (maximal : Ideal (algebraicCharacterRing G)) [maximal.IsMaximal] :
    ¬elementaryInductionIdeal G ≤ maximal := by
  obtain ⟨element, residueIdeal, hmaximal, hevaluation⟩ := algebraicCharacterRing_maximal_evaluation maximal
  let : residueIdeal.IsMaximal := hmaximal
  obtain ⟨prime, hprime, hcharacteristic, hinteger⟩ :=
    complexAlgebraicIntegers_maximal_residue_characteristic residueIdeal
  let : Fact (Nat.Prime prime) := ⟨hprime⟩
  let : CharP (ComplexAlgebraicIntegers ⧸ residueIdeal) prime := hcharacteristic
  obtain ⟨regular, _, hregularOrder, hcongruence⟩ :=
    algebraicCharacterRing_prime_regular_evaluation element residueIdeal prime
  obtain ⟨function, index, hspan, hvalue, hnotdiv⟩ := elementary_delta_witness regular prime hregularOrder
  have hcharacterSpan := extendedElementaryInductionSpan_le_characterSpan hspan
  let lifted : algebraicCharacterRing G :=
    ⟨algebraicCharacterFunction function hcharacterSpan,
      algebraicCharacterFunction_mem function hcharacterSpan⟩
  have hinside : lifted ∈ elementaryInductionIdeal G := hspan
  intro hle
  have hmember : (lifted : G → ComplexAlgebraicIntegers) element ∈ residueIdeal := by
    have hmaximalMember := hle hinside
    rw [hevaluation] at hmaximalMember
    exact hmaximalMember
  have hregularMember : (lifted : G → ComplexAlgebraicIntegers) regular ∈ residueIdeal := by
    have hcongruent := hcongruence lifted
    have hsub := residueIdeal.sub_mem hmember hcongruent
    simpa only [sub_sub_cancel] using hsub
  have hequal : (lifted : G → ComplexAlgebraicIntegers) regular = (index : ComplexAlgebraicIntegers) := by
    apply Subtype.ext
    exact hvalue
  rw [hequal] at hregularMember
  have hdiv := (hinteger (index : ℤ)).mp hregularMember
  exact hnotdiv (Int.natCast_dvd_natCast.mp hdiv)

theorem elementaryInductionIdeal_eq_top {G : Type*} [Group G] [Fintype G] :
    elementaryInductionIdeal G = ⊤ := by
  by_contra hproper
  obtain ⟨maximal, hmaximal, hle⟩ := Ideal.exists_le_maximal (elementaryInductionIdeal G) hproper
  let : maximal.IsMaximal := hmaximal
  exact elementaryInductionIdeal_not_le_maximal maximal hle

theorem extendedElementaryInductionSpan_eq_characterSpan {G : Type*} [Group G] [Fintype G] :
    extendedElementaryInductionSpan G = algebraicCharacterSpan G := by
  apply le_antisymm extendedElementaryInductionSpan_le_characterSpan
  intro function hspan
  let lifted : algebraicCharacterRing G :=
    ⟨algebraicCharacterFunction function hspan, algebraicCharacterFunction_mem function hspan⟩
  have hmember : lifted ∈ elementaryInductionIdeal G := by
    rw [elementaryInductionIdeal_eq_top]
    trivial
  exact hmember

end CFSG.TwoRankLowerBound.Helpers
