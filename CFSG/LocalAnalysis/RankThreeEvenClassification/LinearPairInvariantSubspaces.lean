module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalCore

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v w

def linearSubspaceStabilizer {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space]
    (subspace : Submodule field space) : Subgroup (space ≃ₗ[field] space) where
  carrier := {equivalence | subspace.map (equivalence : Module.End field space) = subspace}
  one_mem' := by
    simp only [Set.mem_ofPred_eq, LinearEquiv.coe_toLinearMap_one, Submodule.map_id]
  mul_mem' := by
    intro first second hfirst hsecond
    change subspace.map ((first * second : space ≃ₗ[field] space) : Module.End field space) = subspace
    rw [LinearEquiv.coe_toLinearMap_mul]
    change subspace.map ((first : Module.End field space).comp (second : Module.End field space)) = subspace
    rw [Submodule.map_comp, hsecond, hfirst]
  inv_mem' := by
    intro equivalence hequivalence
    exact (Submodule.map_symm_eq_iff equivalence).mpr hequivalence

theorem linear_pair_invariant_subspace {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space]
    (first second : space ≃ₗ[field] space) (subspace : Submodule field space)
    (hfirst : subspace.map (first : Module.End field space) = subspace)
    (hsecond : subspace.map (second : Module.End field space) = subspace) :
    ∀ member : (Subgroup.zpowers first ⊔ Subgroup.zpowers second : Subgroup (space ≃ₗ[field] space)),
      subspace.map (member : Module.End field space) = subspace := by
  have hle : Subgroup.zpowers first ⊔ Subgroup.zpowers second ≤ linearSubspaceStabilizer subspace :=
    sup_le (Subgroup.zpowers_le_of_mem hfirst) (Subgroup.zpowers_le_of_mem hsecond)
  intro member
  exact hle member.property

theorem prime_power_generated_of_surjective {actor : Type u} {target : Type v}
    [Group actor] [Group target] (prime : ℕ) (homomorphism : actor →* target)
    (hsurjective : Function.Surjective homomorphism)
    (hgenerated : Subgroup.closure {member : actor | ∃ exponent : ℕ,
      member ^ (prime ^ exponent) = 1} = ⊤) :
    Subgroup.closure {member : target | ∃ exponent : ℕ,
      member ^ (prime ^ exponent) = 1} = ⊤ := by
  apply top_unique
  rw [← Subgroup.map_top_of_surjective homomorphism hsurjective, ← hgenerated, MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro member ⟨preimage, ⟨exponent, hpower⟩, rfl⟩
  exact ⟨exponent, by rw [← map_pow, hpower, map_one]⟩

theorem pair_prime_power_generated {actor : Type u} [Group actor]
    (prime : ℕ) (first second : actor)
    (hfirst : ∃ exponent : ℕ, first ^ (prime ^ exponent) = 1)
    (hsecond : ∃ exponent : ℕ, second ^ (prime ^ exponent) = 1) :
    Subgroup.closure {member : (Subgroup.zpowers first ⊔ Subgroup.zpowers second : Subgroup actor) |
      ∃ exponent : ℕ, member ^ (prime ^ exponent) = 1} = ⊤ := by
  let pair := Subgroup.zpowers first ⊔ Subgroup.zpowers second
  let generated := Subgroup.closure {member : pair | ∃ exponent : ℕ,
    member ^ (prime ^ exponent) = 1}
  let firstMember : pair := ⟨first, Subgroup.mem_sup_left (Subgroup.mem_zpowers first)⟩
  let secondMember : pair := ⟨second, Subgroup.mem_sup_right (Subgroup.mem_zpowers second)⟩
  have hfirstGenerated : firstMember ∈ generated := by
    apply Subgroup.subset_closure
    obtain ⟨exponent, hpower⟩ := hfirst
    exact ⟨exponent, Subtype.ext hpower⟩
  have hsecondGenerated : secondMember ∈ generated := by
    apply Subgroup.subset_closure
    obtain ⟨exponent, hpower⟩ := hsecond
    exact ⟨exponent, Subtype.ext hpower⟩
  have hmap : generated.map pair.subtype = pair := by
    apply le_antisymm (Subgroup.map_subtype_le generated)
    exact sup_le
      (Subgroup.zpowers_le_of_mem (Subgroup.mem_map_of_mem pair.subtype hfirstGenerated))
      (Subgroup.zpowers_le_of_mem (Subgroup.mem_map_of_mem pair.subtype hsecondGenerated))
  apply (Subgroup.map_injective pair.subtype_injective)
  change generated.map pair.subtype = (⊤ : Subgroup pair).map pair.subtype
  rw [hmap]
  ext member
  exact ⟨fun hmember => ⟨⟨member, hmember⟩, Subgroup.mem_top _, rfl⟩,
    fun ⟨preimage, _, heq⟩ => heq ▸ preimage.property⟩

theorem odd_card_range_of_odd_domain {actor : Type u} {target : Type v}
    [Group actor] [Group target] (homomorphism : actor →* target) (hodd : Odd (Nat.card actor)) :
    Odd (Nat.card homomorphism.range) := by
  have hdivides := homomorphism.ker.card_quotient_dvd_card
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange homomorphism).toEquiv] at hdivides
  exact hodd.of_dvd_nat hdivides

end CFSG.RankThreeEvenClassification.Helpers
