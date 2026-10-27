module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.QuadraticIrreducibleDimension
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableQuadraticPlane

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem solvable_quadratic_pair_reducible {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space] [IsAlgClosed field]
    [FiniteDimensional field space] (hdimension : 2 ≤ Module.finrank field space)
    (prime : ℕ) (hprime : prime.Prime) (hodd : Odd prime) [CharP field prime]
    (first second : space ≃ₗ[field] space)
    (hfirst : ((first : Module.End field space) - LinearMap.id) ^ 2 = 0)
    (hsecond : ((second : Module.End field space) - LinearMap.id) ^ 2 = 0)
    [Finite (Subgroup.zpowers first ⊔ Subgroup.zpowers second : Subgroup (space ≃ₗ[field] space))]
    [Group.IsSolvable (Subgroup.zpowers first ⊔ Subgroup.zpowers second : Subgroup (space ≃ₗ[field] space))]
    (halternative : 5 ≤ prime ∨
      Odd (Nat.card (Subgroup.zpowers first ⊔ Subgroup.zpowers second : Subgroup (space ≃ₗ[field] space)))) :
    ∃ subspace : Submodule field space, subspace ≠ ⊥ ∧ subspace ≠ ⊤ ∧
      subspace.map (first : Module.End field space) = subspace ∧
        subspace.map (second : Module.End field space) = subspace := by
  classical
  by_contra hnone
  have hirreducible : ∀ subspace : Submodule field space,
      subspace.map (first : Module.End field space) = subspace →
      subspace.map (second : Module.End field space) = subspace → subspace = ⊥ ∨ subspace = ⊤ := by
    intro subspace hfirstMap hsecondMap
    by_cases hbot : subspace = ⊥
    · exact Or.inl hbot
    · right
      by_contra htop
      exact hnone ⟨subspace, hbot, htop, hfirstMap, hsecondMap⟩
  have : Nontrivial space := Module.finrank_pos_iff.mp (by
    show 0 < Module.finrank field space
    omega)
  have hupper := quadratic_pair_irreducible_dimension first second hfirst hsecond hirreducible
  have hplane : Module.finrank field space = 2 := by omega
  obtain ⟨vector, hvectorNe, hfirstFixed, hsecondFixed⟩ :=
    solvable_quadratic_plane_common_fixed_vector hplane prime hprime hodd first second hfirst hsecond halternative
  let line := Submodule.span field {vector}
  have hlineDimension : Module.finrank field line = 1 := finrank_span_singleton hvectorNe
  have hlineBot : line ≠ ⊥ := by
    intro heq
    rw [heq, finrank_bot] at hlineDimension
    omega
  have hlineTop : line ≠ ⊤ := by
    intro heq
    rw [heq, finrank_top, hplane] at hlineDimension
    omega
  apply hnone
  refine ⟨line, hlineBot, hlineTop, ?_, ?_⟩
  · apply linear_invariant_submodule_map_eq
    intro member hmember
    obtain ⟨scalar, rfl⟩ := Submodule.mem_span_singleton.mp hmember
    rw [map_smul, hfirstFixed]
    exact Submodule.mem_span_singleton.mpr ⟨scalar, rfl⟩
  · apply linear_invariant_submodule_map_eq
    intro member hmember
    obtain ⟨scalar, rfl⟩ := Submodule.mem_span_singleton.mp hmember
    rw [map_smul, hsecondFixed]
    exact Submodule.mem_span_singleton.mpr ⟨scalar, rfl⟩

end CFSG.RankThreeEvenClassification.Helpers
