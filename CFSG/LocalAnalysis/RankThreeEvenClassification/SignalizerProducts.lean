module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerCommonFixed
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeProductFixed

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem SignalizerCompatible.normalized_sup {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hpgroup : IsPGroup prime actor) (first second : Subgroup G)
    (hfirst : SignalizerCompatible prime actor signalizer first)
    (hsecond : SignalizerCompatible prime actor signalizer second)
    (hnormalizes : second ≤ Subgroup.normalizer (first : Set G)) :
    SignalizerCompatible prime actor signalizer (first ⊔ second) := by
  refine ⟨(le_inf hfirst.normalized hsecond.normalized).trans
      (Subgroup.inf_normalizer_le_normalizer_sup first second),
    normalized_sup_solvable first second hnormalizes hfirst.solvable hsecond.solvable,
    normalized_sup_prime_complement prime hprime first second hnormalizes
      hfirst.primeComplement hsecond.primeComplement, ?_⟩
  intro element helement hne
  have hcyclicPGroup : IsPGroup prime (Subgroup.zpowers element) :=
    hpgroup.of_injective (Subgroup.inclusion (Subgroup.zpowers_le_of_mem helement))
      (Subgroup.inclusion_injective (Subgroup.zpowers_le_of_mem helement))
  have hfixed := normalized_sup_centralizer_eq_of_pGroup_prime_complement prime hprime
    (Subgroup.zpowers element) first second hcyclicPGroup
      ((Subgroup.zpowers_le_of_mem helement).trans hfirst.normalized)
      ((Subgroup.zpowers_le_of_mem helement).trans hsecond.normalized) hnormalizes
      (fun hdiv => hfirst.primeComplement (hdiv.trans (Subgroup.card_dvd_of_le inf_le_left)))
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hfixed
  rw [hfixed]
  exact sup_le (hfirst.fixed_le element helement hne) (hsecond.fixed_le element helement hne)

theorem signalizerCommonFixed_normalizes_value {G : Type u} [Group G]
    (actor : Subgroup G) (signalizer : G → Subgroup G)
    (element : G) (hmem : element ∈ actor) (hne : element ≠ 1) :
    signalizerCommonFixed actor signalizer ≤ Subgroup.normalizer (signalizer element : Set G) :=
  (signalizerCommonFixed_le_value actor signalizer element hmem hne).trans Subgroup.le_normalizer

theorem signalizerCommonFixed_normalizes_generated {G : Type u} [Group G]
    (actor : Subgroup G) (signalizer : G → Subgroup G) :
    signalizerCommonFixed actor signalizer ≤
      Subgroup.normalizer (signalizerGenerated actor signalizer : Set G) := by
  apply normalizes_iSup
  intro element
  apply normalizes_iSup
  intro hmem
  apply normalizes_iSup
  intro hne
  exact signalizerCommonFixed_normalizes_value actor signalizer element hmem hne

theorem SignalizerCompatible.map_of_actor_fixed {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (subgroup : Subgroup G) (hcompatible : SignalizerCompatible prime actor signalizer subgroup)
    (automorphism : G ≃* G) (hactor : ∀ element ∈ actor, automorphism element = element)
    (hvalues : ∀ element ∈ actor, element ≠ 1 →
      (signalizer element).map automorphism.toMonoidHom = signalizer element) :
    SignalizerCompatible prime actor signalizer (subgroup.map automorphism.toMonoidHom) := by
  have : Group.IsSolvable subgroup := hcompatible.solvable
  refine ⟨?_, Group.isSolvable_of_surjective
      (f := (automorphism.subgroupMap subgroup).toMonoidHom)
        (automorphism.subgroupMap subgroup).surjective, ?_, ?_⟩
  · intro element helement
    rw [← Subgroup.map_normalizer_eq_of_bijective subgroup automorphism.bijective]
    exact Subgroup.mem_map.mpr ⟨element, hcompatible.normalized helement, hactor element helement⟩
  · rw [Subgroup.card_map_of_injective (f := automorphism.toMonoidHom) automorphism.injective]
    exact hcompatible.primeComplement
  · intro element helement hne other hother
    obtain ⟨preimage, hpreimage, hpreimageEq⟩ := Subgroup.mem_map.mp hother.1
    have hpreimageFixed : preimage ∈ Subgroup.centralizer ({element} : Set G) := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      apply automorphism.injective
      rw [map_mul, map_mul, hactor element helement]
      change automorphism.toMonoidHom preimage * element = element * automorphism.toMonoidHom preimage
      rw [hpreimageEq]
      exact Subgroup.mem_centralizer_singleton_iff.mp hother.2
    have hpreimageSignalizer := hcompatible.fixed_le element helement hne ⟨hpreimage, hpreimageFixed⟩
    have hmapped := Subgroup.mem_map_of_mem automorphism.toMonoidHom hpreimageSignalizer
    rw [hvalues element helement hne] at hmapped
    exact hpreimageEq ▸ hmapped

theorem SignalizerCompatible.conjugate_by_common_fixed {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer)
    (subgroup : Subgroup G) (hcompatible : SignalizerCompatible prime actor signalizer subgroup)
    (conjugator : G) (hconjugator : conjugator ∈ signalizerCommonFixed actor signalizer) :
    SignalizerCompatible prime actor signalizer (subgroup.map (MulAut.conj conjugator).toMonoidHom) := by
  have hcentralizer := signalizerCommonFixed_le_centralizer prime actor actor signalizer hsignalizer
    le_rfl hconjugator
  apply SignalizerCompatible.map_of_actor_fixed prime actor signalizer subgroup hcompatible
    (MulAut.conj conjugator)
  · intro element helement
    change conjugator * element * conjugator⁻¹ = element
    rw [← Subgroup.mem_centralizer_iff.mp hcentralizer element helement, mul_inv_cancel_right]
  · intro element helement hne
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (signalizerCommonFixed_normalizes_value actor signalizer element helement hne hconjugator)

end CFSG.RankThreeEvenClassification.Helpers
