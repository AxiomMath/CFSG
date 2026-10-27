module

public import CFSG.CharacterTheory.TwoRankLowerBound.FiniteCharacters

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

universe groupUniverse

@[expose] def virtualCharacters (G : Type groupUniverse) [Group G] : Submodule ℤ (G → ℂ) :=
  Submodule.span ℤ (Set.range fun data : FiniteComplexRepresentation.{groupUniverse, groupUniverse} G =>
    data.character)

@[expose] def irreducibleVirtualCharacters (G : Type groupUniverse) [Group G] : Submodule ℤ (G → ℂ) :=
  Submodule.span ℤ {character | ∃ data : FiniteComplexRepresentation.{groupUniverse, groupUniverse} G,
    data.IsIrreducible ∧ data.character = character}

theorem character_mem_virtualCharacters {G : Type groupUniverse} [Group G]
    (data : FiniteComplexRepresentation.{groupUniverse, groupUniverse} G) :
    data.character ∈ virtualCharacters G :=
  Submodule.subset_span ⟨data, rfl⟩

theorem character_mem_irreducibleVirtualCharacters {G : Type groupUniverse} [Group G] [Finite G]
    (data : FiniteComplexRepresentation.{groupUniverse, groupUniverse} G) :
    data.character ∈ irreducibleVirtualCharacters G := by
  obtain ⟨size, summand, hsimple, hsum⟩ :=
    finiteComplexRepresentation_exists_irreducible_character_sum data
  have hsumFunction : data.character = ∑ label : Fin size, (summand label).character := by
    ext element
    simpa using hsum element
  rw [hsumFunction]
  apply Submodule.sum_mem
  intro label _
  exact Submodule.subset_span ⟨summand label, hsimple label, rfl⟩

theorem virtualCharacters_eq_irreducible {G : Type groupUniverse} [Group G] [Finite G] :
    virtualCharacters G = irreducibleVirtualCharacters G := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨data, rfl⟩
    exact character_mem_irreducibleVirtualCharacters data
  · apply Submodule.span_le.mpr
    rintro _ ⟨data, _, rfl⟩
    exact character_mem_virtualCharacters data

@[expose] noncomputable def inducedFunctionLinearMap {G : Type*} [Group G] [Fintype G]
    (subgroup : Subgroup G) : (subgroup → ℂ) →ₗ[ℤ] (G → ℂ) :=
  { toFun := inducedFunction subgroup
    map_add' := by
      intro left right
      ext element
      unfold inducedFunction
      simp only [Pi.add_apply, ← mul_add, ← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro conjugator _
      split_ifs <;> simp
    map_smul' := by
      intro scalar function
      ext element
      unfold inducedFunction
      simp only [Pi.smul_apply, RingHom.id_apply, zsmul_eq_mul]
      have hsum :
          (∑ conjugator : G,
            if hmember : conjugator⁻¹ * element * conjugator ∈ subgroup then
              (scalar : ℂ) * function ⟨conjugator⁻¹ * element * conjugator, hmember⟩ else 0) =
            (scalar : ℂ) * ∑ conjugator : G,
              if hmember : conjugator⁻¹ * element * conjugator ∈ subgroup then
                function ⟨conjugator⁻¹ * element * conjugator, hmember⟩ else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro conjugator _
        split_ifs <;> simp
      rw [hsum]
      ring }

theorem inducedFunction_mem_virtualCharacters {G : Type groupUniverse} [Group G] [Fintype G]
    (subgroup : Subgroup G) {function : subgroup → ℂ}
    (hvirtual : function ∈ virtualCharacters subgroup) :
    inducedFunction subgroup function ∈ virtualCharacters G := by
  have hmap : virtualCharacters subgroup ≤
      (virtualCharacters G).comap (inducedFunctionLinearMap subgroup) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨data, rfl⟩
    have hequal : inducedFunction subgroup data.character =
        (coinducedFiniteComplexRepresentation subgroup data).character := by
      ext element
      exact (coinducedFiniteComplexRepresentation_character subgroup data element).symm
    change inducedFunction subgroup data.character ∈ virtualCharacters G
    rw [hequal]
    exact character_mem_virtualCharacters _
  exact hmap hvirtual

set_option backward.isDefEq.respectTransparency false in
theorem virtualCharacter_exists_distinct_irreducible_expansion
    {G : Type groupUniverse} [Group G] [Finite G] {function : G → ℂ}
    (hvirtual : function ∈ virtualCharacters G) :
    ∃ (support : Finset (G → ℂ)) (coefficient : (G → ℂ) → ℤ),
      (∀ character ∈ support,
        ∃ data : FiniteComplexRepresentation.{groupUniverse, groupUniverse} G,
          data.IsIrreducible ∧ data.character = character) ∧
      ∀ element : G,
        function element = ∑ character ∈ support, (coefficient character : ℂ) * character element := by
  rw [virtualCharacters_eq_irreducible] at hvirtual
  obtain ⟨coefficient, support, hsupport, _, hsum⟩ :=
    Submodule.mem_span_iff_exists_finset_subset.mp hvirtual
  refine ⟨support, coefficient, hsupport, ?_⟩
  intro element
  have heval := congrFun hsum element
  simpa [Finset.sum_apply, Pi.smul_apply, zsmul_eq_mul] using heval.symm

end CFSG.TwoRankLowerBound.Helpers
