module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaPlaneExactQuotient
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem signalizer_complete_iff_mapped_complete_of_compatible_kernel
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hsurjective : Function.Surjective homomorphism)
    (actor plane : Subgroup G) (signalizer : G → Subgroup G)
    (hpgroup : IsPGroup prime actor) (hplaneLe : plane ≤ actor)
    (hpower : ∀ member : plane, member ^ prime = 1) (hplaneCard : Nat.card plane = prime ^ 2)
    (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer)
    (hkernelCompatible : SignalizerCompatible prime actor signalizer homomorphism.ker)
    (hinjective : Set.InjOn homomorphism (actor : Set G)) :
    SignalizerComplete prime actor signalizer ↔
      SignalizerComplete prime (actor.map homomorphism) (mappedSignalizer homomorphism actor signalizer) := by
  constructor
  · exact SignalizerComplete.map prime hprime homomorphism actor signalizer hpgroup hinjective
  · intro hcomplete
    let preimage := (signalizerGenerated (actor.map homomorphism)
      (mappedSignalizer homomorphism actor signalizer)).comap homomorphism
    have hpreimage := SignalizerCompatible.comap prime hprime homomorphism hsurjective actor signalizer
      hpgroup hsignalizer hkernelCompatible _ hcomplete hinjective
    have hpreimageLe : preimage ≤ signalizerGenerated actor signalizer :=
      SignalizerCompatible.le_generated prime hprime actor plane signalizer hplaneLe hpower hplaneCard
        preimage hpreimage
    have hgeneratedLe : signalizerGenerated actor signalizer ≤ preimage := by
      apply Subgroup.map_le_iff_le_comap.mp
      rw [signalizerGenerated_map_eq homomorphism actor signalizer hinjective]
    have heq : preimage = signalizerGenerated actor signalizer := le_antisymm hpreimageLe hgeneratedLe
    change SignalizerCompatible prime actor signalizer (signalizerGenerated actor signalizer)
    change SignalizerCompatible prime actor signalizer preimage at hpreimage
    rw [heq] at hpreimage
    exact hpreimage

theorem signalizer_completion_comap_eq_of_compatible_kernel
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (actor plane : Subgroup G) (signalizer : G → Subgroup G)
    (hplaneLe : plane ≤ actor) (hpower : ∀ member : plane, member ^ prime = 1)
    (hplaneCard : Nat.card plane = prime ^ 2)
    (hkernelCompatible : SignalizerCompatible prime actor signalizer homomorphism.ker)
    (hinjective : Set.InjOn homomorphism (actor : Set G)) :
    (signalizerGenerated (actor.map homomorphism) (mappedSignalizer homomorphism actor signalizer)).comap
      homomorphism = signalizerGenerated actor signalizer := by
  rw [← signalizerGenerated_map_eq homomorphism actor signalizer hinjective]
  exact Subgroup.comap_map_eq_self
    (SignalizerCompatible.le_generated prime hprime actor plane signalizer hplaneLe hpower hplaneCard
      homomorphism.ker hkernelCompatible)

theorem quotient_actor_injOn_of_compatible_kernel
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor kernel : Subgroup G) [kernel.Normal]
    (signalizer : G → Subgroup G) (hpgroup : IsPGroup prime actor)
    (hcompatible : SignalizerCompatible prime actor signalizer kernel) :
    Set.InjOn (QuotientGroup.mk' kernel) (actor : Set G) := by
  apply injOn_pSubgroup_of_prime_complement_kernel prime hprime (QuotientGroup.mk' kernel)
    (by rw [QuotientGroup.ker_mk']; exact hcompatible.primeComplement) actor hpgroup

theorem signalizer_complete_iff_quotient_complete
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor plane kernel : Subgroup G) [kernel.Normal]
    (signalizer : G → Subgroup G) (hpgroup : IsPGroup prime actor)
    (hplaneLe : plane ≤ actor) (hpower : ∀ member : plane, member ^ prime = 1)
    (hplaneCard : Nat.card plane = prime ^ 2)
    (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer)
    (hkernelCompatible : SignalizerCompatible prime actor signalizer kernel) :
    SignalizerComplete prime actor signalizer ↔
      SignalizerComplete prime (actor.map (QuotientGroup.mk' kernel))
        (mappedSignalizer (QuotientGroup.mk' kernel) actor signalizer) := by
  apply signalizer_complete_iff_mapped_complete_of_compatible_kernel prime hprime
    (QuotientGroup.mk' kernel) (QuotientGroup.mk'_surjective kernel) actor plane signalizer hpgroup
      hplaneLe hpower hplaneCard hsignalizer
  · rw [QuotientGroup.ker_mk']
    exact hkernelCompatible
  · exact quotient_actor_injOn_of_compatible_kernel prime hprime actor kernel signalizer hpgroup
      hkernelCompatible

end CFSG.RankThreeEvenClassification.Helpers
