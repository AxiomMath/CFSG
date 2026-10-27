module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.PrimePairPermutations
public import CFSG.LocalAnalysis.RankThreeEvenClassification.PrimeElementLifting

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem projective_pElement_plane_preserving_pair_eq_one {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space] [IsAlgClosed field]
    [FiniteDimensional field space] (hdimension : Module.finrank field space = 2)
    (prime : ℕ) (hprime : prime.Prime) (hodd : Odd prime) [CharP field prime]
    (subgroup : Subgroup (space ≃ₗ[field] space)) [Finite subgroup]
    (member : ((linearProjectiveAction field space).comp subgroup.subtype).range)
    (exponent : ℕ) (hpower : member ^ (prime ^ exponent) = 1)
    (first second : Projectivization field space) (hne : first ≠ second)
    (hpreserves : ∀ point : Projectivization field space,
      (member : Equiv.Perm (Projectivization field space)) point ∈
        ({first, second} : Set (Projectivization field space)) ↔
          point ∈ ({first, second} : Set (Projectivization field space))) : member = 1 := by
  have hpowerAmbient : (member : Equiv.Perm (Projectivization field space)) ^ (prime ^ exponent) = 1 :=
    congrArg (((linearProjectiveAction field space).comp subgroup.subtype).range.subtype) hpower
  obtain ⟨hfirst, hsecond⟩ := prime_power_permutation_preserving_pair_fixes prime hodd
    (member : Equiv.Perm (Projectivization field space)) exponent hpowerAmbient first second hne hpreserves
  by_contra hmemberNe
  obtain ⟨point, _, hunique⟩ := projective_pElement_plane_has_unique_fixed_point hdimension prime hprime
    subgroup member hmemberNe exponent hpower
  exact hne ((hunique first hfirst).trans (hunique second hsecond).symm)

theorem projective_prime_generated_plane_cannot_preserve_pair {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space] [IsAlgClosed field]
    [FiniteDimensional field space] (hdimension : Module.finrank field space = 2)
    (prime : ℕ) (hprime : prime.Prime) (hodd : Odd prime) [CharP field prime]
    (subgroup : Subgroup (space ≃ₗ[field] space)) [Finite subgroup]
    (projectiveSubgroup : Subgroup ((linearProjectiveAction field space).comp subgroup.subtype).range)
    [Nontrivial projectiveSubgroup]
    (hgenerated : Subgroup.closure {member : projectiveSubgroup | ∃ exponent : ℕ,
      member ^ (prime ^ exponent) = 1} = ⊤)
    (first second : Projectivization field space) (hne : first ≠ second)
    (hpreserves : ∀ member : projectiveSubgroup, ∀ point : Projectivization field space,
      (member : Equiv.Perm (Projectivization field space)) point ∈
        ({first, second} : Set (Projectivization field space)) ↔
          point ∈ ({first, second} : Set (Projectivization field space))) : False := by
  have htrivial : (⊤ : Subgroup projectiveSubgroup) ≤ ⊥ := by
    rw [← hgenerated]
    apply (Subgroup.closure_le ⊥).mpr
    rintro member ⟨exponent, hpower⟩
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    exact projective_pElement_plane_preserving_pair_eq_one hdimension prime hprime hodd subgroup
      member exponent (congrArg projectiveSubgroup.subtype hpower) first second hne (hpreserves member)
  exact top_ne_bot (le_antisymm htrivial bot_le)

end CFSG.RankThreeEvenClassification.Helpers
