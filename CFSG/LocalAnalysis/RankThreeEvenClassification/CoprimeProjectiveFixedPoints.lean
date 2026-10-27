module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.PrimeElementLifting
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SemisimpleProjectivePairs

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem projective_coprime_pElement_plane_has_fixed_pair {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space] [IsAlgClosed field]
    [FiniteDimensional field space] (hdimension : Module.finrank field space = 2)
    (characteristic prime : ℕ) (hcharacteristic : characteristic.Prime) (hprime : prime.Prime)
    (hdistinct : characteristic ≠ prime) [CharP field characteristic]
    (subgroup : Subgroup (space ≃ₗ[field] space)) [Finite subgroup]
    (member : ((linearProjectiveAction field space).comp subgroup.subtype).range)
    (hne : member ≠ 1) (exponent : ℕ) (hpower : member ^ (prime ^ exponent) = 1) :
    ∃ first second : Projectivization field space, first ≠ second ∧
      ∀ point : Projectivization field space,
        (member : Equiv.Perm (Projectivization field space)) point = point ↔
          point = first ∨ point = second := by
  let action := (linearProjectiveAction field space).comp subgroup.subtype
  obtain ⟨preimage, heq, dimension, hpreimagePower⟩ := prime_power_element_lifts_surjective prime hprime
    action.rangeRestrict action.rangeRestrict_surjective member exponent hpower
  have hpowerAmbient : (preimage : space ≃ₗ[field] space) ^ (prime ^ dimension) = 1 :=
    congrArg (fun value : subgroup => (value : space ≃ₗ[field] space)) hpreimagePower
  have hcoprime : ¬characteristic ∣ prime ^ dimension := by
    intro hdivides
    exact hdistinct ((Nat.prime_dvd_prime_iff_eq hcharacteristic hprime).mp
      (hcharacteristic.dvd_of_dvd_pow hdivides))
  have hsemisimple := linear_coprime_power_isSemisimple characteristic
    (preimage : space ≃ₗ[field] space) (prime ^ dimension) hcoprime hpowerAmbient
  have hprojectiveEq : linearProjectiveAction field space (preimage : space ≃ₗ[field] space) =
      (member : Equiv.Perm (Projectivization field space)) := congrArg Subtype.val heq
  have hprojectiveNe : linearProjectiveAction field space (preimage : space ≃ₗ[field] space) ≠ 1 := by
    intro hone
    apply hne
    apply Subtype.ext
    exact hprojectiveEq.symm.trans hone
  obtain ⟨first, second, hpointsNe, hfixed⟩ :=
    semisimple_plane_nonidentity_projective_has_fixed_pair hdimension
      (preimage : space ≃ₗ[field] space) hsemisimple hprojectiveNe
  rw [hprojectiveEq] at hfixed
  exact ⟨first, second, hpointsNe, hfixed⟩

theorem commuting_permutation_preserves_fixed_pair {points : Type u}
    (member conjugator : Equiv.Perm points) (hcommute : Commute member conjugator)
    (first second : points)
    (hfixed : ∀ point : points, member point = point ↔ point = first ∨ point = second) :
    ∀ point : points, conjugator point ∈ ({first, second} : Set points) ↔
      point ∈ ({first, second} : Set points) := by
  intro point
  have hcommuting : member (conjugator point) = conjugator (member point) :=
    congrArg (fun permutation : Equiv.Perm points => permutation point) hcommute.eq
  have hiff : member (conjugator point) = conjugator point ↔ member point = point := by
    rw [hcommuting]
    exact conjugator.injective.eq_iff
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, hfixed] using hiff

end CFSG.RankThreeEvenClassification.Helpers
