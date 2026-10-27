module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ProjectivePrimeFixedPoints

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem prime_power_element_lifts_surjective {G : Type u} {H : Type v}
    [Group G] [Group H] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (homomorphism : G →* H) (hsurjective : Function.Surjective homomorphism)
    (member : H) (exponent : ℕ) (hpower : member ^ (prime ^ exponent) = 1) :
    ∃ preimage : G, homomorphism preimage = member ∧
      ∃ dimension : ℕ, preimage ^ (prime ^ dimension) = 1 := by
  have : Fact prime.Prime := ⟨hprime⟩
  have hcyclic : IsPGroup prime (Subgroup.zpowers member) := by
    apply IsPGroup.of_card_dvd_pow (n := exponent)
    rw [Nat.card_zpowers]
    exact orderOf_dvd_iff_pow_eq_one.mpr hpower
  obtain ⟨targetSylow, htargetLe⟩ := hcyclic.exists_le_sylow
  obtain ⟨sourceSylow, hsource⟩ := Sylow.mapSurjective_surjective hsurjective prime targetSylow
  have hmem : member ∈ (targetSylow : Subgroup H) := htargetLe (Subgroup.mem_zpowers member)
  rw [← hsource, Sylow.coe_mapSurjective] at hmem
  obtain ⟨preimage, hpreimage, heq⟩ := hmem
  obtain ⟨dimension, hcard⟩ := sourceSylow.isPGroup'.exists_card_eq
  have hinternalPower : (⟨preimage, hpreimage⟩ : (sourceSylow : Subgroup G)) ^ (prime ^ dimension) = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  exact ⟨preimage, heq, dimension,
    congrArg (fun value : (sourceSylow : Subgroup G) => (value : G)) hinternalPower⟩

theorem projective_pElement_plane_has_unique_fixed_point {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space] [IsAlgClosed field]
    [FiniteDimensional field space] (hdimension : Module.finrank field space = 2)
    (prime : ℕ) (hprime : prime.Prime) [CharP field prime]
    (subgroup : Subgroup (space ≃ₗ[field] space)) [Finite subgroup]
    (member : ((linearProjectiveAction field space).comp subgroup.subtype).range)
    (hne : member ≠ 1) (exponent : ℕ) (hpower : member ^ (prime ^ exponent) = 1) :
    ∃! point : Projectivization field space, (member : Equiv.Perm (Projectivization field space)) point = point := by
  let action := (linearProjectiveAction field space).comp subgroup.subtype
  obtain ⟨preimage, heq, dimension, hpreimagePower⟩ := prime_power_element_lifts_surjective prime hprime
    action.rangeRestrict action.rangeRestrict_surjective member exponent hpower
  have hpreimageNe : (preimage : space ≃ₗ[field] space) ≠ 1 := by
    intro hzero
    have hpreimageOne : preimage = 1 := Subtype.ext hzero
    rw [hpreimageOne, map_one] at heq
    exact hne heq.symm
  have hpowerAmbient : (preimage : space ≃ₗ[field] space) ^ (prime ^ dimension) = 1 :=
    congrArg (fun value : subgroup => (value : space ≃ₗ[field] space)) hpreimagePower
  have hunique := linear_pElement_plane_has_unique_projective_fixed_point hdimension prime hprime
    (preimage : space ≃ₗ[field] space) hpreimageNe dimension hpowerAmbient
  have hambient : linearProjectiveAction field space (preimage : space ≃ₗ[field] space) = member :=
    congrArg (fun value : action.range => (value : Equiv.Perm (Projectivization field space))) heq
  rw [hambient] at hunique
  exact hunique

end CFSG.RankThreeEvenClassification.Helpers
