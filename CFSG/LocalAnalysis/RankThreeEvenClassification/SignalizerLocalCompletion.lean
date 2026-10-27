module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerMinimality

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

@[expose] noncomputable def signalizerRestrictedGenerated {G : Type u} [Group G]
    (actor : Subgroup G) (signalizer : G → Subgroup G) (overgroup : Subgroup G) : Subgroup G :=
  ⨆ (element : G) (_ : element ∈ actor) (_ : element ≠ 1), signalizer element ⊓ overgroup

theorem signalizerRestrictedGenerated_le {G : Type u} [Group G]
    (actor : Subgroup G) (signalizer : G → Subgroup G) (overgroup : Subgroup G) :
    signalizerRestrictedGenerated actor signalizer overgroup ≤ overgroup := by
  apply iSup_le
  intro element
  apply iSup_le
  intro hmem
  apply iSup_le
  intro hne
  exact inf_le_right

theorem signalizerRestrictedGenerated_conjugation {G : Type u} [Group G]
    (actor : Subgroup G) (signalizer : G → Subgroup G) (overgroup : Subgroup G)
    (conjugator : G) (hconjugator : conjugator ∈ signalizerCommonFixed actor signalizer) :
    (signalizerRestrictedGenerated actor signalizer overgroup).map (MulAut.conj conjugator).toMonoidHom =
      signalizerRestrictedGenerated actor signalizer (overgroup.map (MulAut.conj conjugator).toMonoidHom) := by
  simp only [signalizerRestrictedGenerated, Subgroup.map_iSup]
  apply congrArg
  funext element
  apply congrArg
  funext hmem
  apply congrArg
  funext hne
  rw [Subgroup.map_inf _ _ _ (MulAut.conj conjugator).injective]
  have hfixed : (signalizer element).map (MulAut.conj conjugator).toMonoidHom = signalizer element :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (signalizerCommonFixed_normalizes_value actor signalizer element hmem hne hconjugator)
  rw [hfixed]

theorem SignalizerLocallyComplete.normalizer_completion_compatible {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hlocal : SignalizerLocallyComplete prime actor signalizer)
    (subgroup : Subgroup G) (hcompatible : SignalizerCompatible prime actor signalizer subgroup)
    (hne : subgroup ≠ ⊥) :
    SignalizerCompatible prime actor signalizer
      (signalizerRestrictedGenerated actor signalizer (Subgroup.normalizer (subgroup : Set G))) := by
  have hcomplete := hlocal.1 subgroup hcompatible hne
  have hambient := (signalizer_compatible_restriction_iff prime actor
    (Subgroup.normalizer (subgroup : Set G)) signalizer hcompatible.normalized _).mp hcomplete
  rw [signalizerGenerated_restriction_map_eq actor _ signalizer hcompatible.normalized] at hambient
  exact hambient

theorem compatible_le_normalizer_completion {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor plane : Subgroup G) (signalizer : G → Subgroup G)
    (hplaneLe : plane ≤ actor) (hpower : ∀ member : plane, member ^ prime = 1)
    (hplaneCard : Nat.card plane = prime ^ 2)
    (subgroup other : Subgroup G) (hcompatible : SignalizerCompatible prime actor signalizer subgroup)
    (hother : SignalizerCompatible prime actor signalizer other)
    (hle : other ≤ Subgroup.normalizer (subgroup : Set G)) :
    other ≤ signalizerRestrictedGenerated actor signalizer (Subgroup.normalizer (subgroup : Set G)) := by
  have hle := compatible_subgroup_le_restriction_completion prime hprime actor plane
    (Subgroup.normalizer (subgroup : Set G)) signalizer hcompatible.normalized hplaneLe hpower hplaneCard
      other hother hle
  rw [signalizerGenerated_restriction_map_eq actor _ signalizer hcompatible.normalized] at hle
  exact hle

theorem compatible_normal_in_normalizer_completion {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor plane : Subgroup G) (signalizer : G → Subgroup G)
    (hplaneLe : plane ≤ actor) (hpower : ∀ member : plane, member ^ prime = 1)
    (hplaneCard : Nat.card plane = prime ^ 2)
    (subgroup : Subgroup G) (hcompatible : SignalizerCompatible prime actor signalizer subgroup) :
    subgroup ≤ signalizerRestrictedGenerated actor signalizer (Subgroup.normalizer (subgroup : Set G)) ∧
      (subgroup.subgroupOf
        (signalizerRestrictedGenerated actor signalizer (Subgroup.normalizer (subgroup : Set G)))).Normal := by
  have hle := compatible_le_normalizer_completion prime hprime actor plane signalizer hplaneLe hpower hplaneCard
    subgroup subgroup hcompatible hcompatible Subgroup.le_normalizer
  exact ⟨hle, (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
    (signalizerRestrictedGenerated_le actor signalizer _)⟩

theorem SignalizerCompatible.of_values_le {G : Type u} [Group G]
    (prime : ℕ) (actor : Subgroup G) (first second : G → Subgroup G)
    (hvalues : ∀ element ∈ actor, element ≠ 1 → first element ≤ second element)
    (subgroup : Subgroup G) (hcompatible : SignalizerCompatible prime actor first subgroup) :
    SignalizerCompatible prime actor second subgroup := by
  refine ⟨hcompatible.normalized, hcompatible.solvable, hcompatible.primeComplement, ?_⟩
  intro element hmem hne
  exact (hcompatible.fixed_le element hmem hne).trans (hvalues element hmem hne)

theorem SignalizerLocallyComplete.prime_deleted_completion {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor plane : Subgroup G) (signalizer : G → Subgroup G)
    (hpgroup : IsPGroup prime actor) (hcomm : IsMulCommutative actor)
    (hplaneLe : plane ≤ actor) (hpower : ∀ member : plane, member ^ prime = 1)
    (hplaneCard : Nat.card plane = prime ^ 2)
    (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer)
    (hlocal : SignalizerLocallyComplete prime actor signalizer)
    (deleted : ℕ) (hdeleted : deleted ∈ signalizerSpectrum actor signalizer) :
    let primes := signalizerSpectrum actor signalizer \ {deleted}
    let completion := signalizerGenerated actor (primeSetSignalizer primes actor signalizer)
    SignalizerCompatible prime actor signalizer completion ∧ PrimeSetOrder primes (Nat.card completion) ∧
      signalizerCommonFixed actor signalizer ≤ Subgroup.normalizer (completion : Set G) ∧
      ∀ subgroup : Subgroup G, SignalizerCompatible prime actor signalizer subgroup →
        PrimeSetOrder primes (Nat.card subgroup) →
        signalizerCommonFixed actor signalizer ≤ Subgroup.normalizer (subgroup : Set G) → subgroup ≤ completion := by
  let primes := signalizerSpectrum actor signalizer \ {deleted}
  let completion := signalizerGenerated actor (primeSetSignalizer primes actor signalizer)
  have hcomplete : SignalizerComplete prime actor (primeSetSignalizer primes actor signalizer) :=
    hlocal.2 deleted hdeleted
  refine ⟨SignalizerCompatible.of_values_le prime actor _ signalizer
    (fun element _ _ => primeSetSignalizer_le_value primes actor signalizer element) completion hcomplete, ?_, ?_, ?_⟩
  · intro divisor hdivisor hdiv
    have hmem := SignalizerCompatible.prime_dvd_mem_spectrum prime hprime actor plane
      (primeSetSignalizer primes actor signalizer) hpgroup hplaneLe hpower hplaneCard completion hcomplete
        divisor hdivisor hdiv
    exact (signalizerSpectrum_primeSetSignalizer_subset prime hprime primes actor signalizer hpgroup hsignalizer hmem).1
  · apply normalizes_iSup
    intro element
    apply normalizes_iSup
    intro hmem
    apply normalizes_iSup
    intro hne
    exact primeSetSignalizer_common_fixed_normalized prime hprime primes actor signalizer hpgroup hsignalizer
      element hmem hne
  · intro subgroup hcompatible horder hnormalized
    exact SignalizerCompatible.le_generated prime hprime actor plane (primeSetSignalizer primes actor signalizer)
      hplaneLe hpower hplaneCard subgroup
      (SignalizerCompatible.primeSetSignalizer_of_fixed_normalized prime primes actor signalizer hcomm hsignalizer
        subgroup hcompatible horder hnormalized)

end CFSG.RankThreeEvenClassification.Helpers
