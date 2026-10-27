module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerOnePrimeCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerQuotientCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerSize

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

def SignalizerSizeMinimal {G : Type u} [Group G]
    (prime : ℕ) (actor : Subgroup G) (signalizer : G → Subgroup G) : Prop :=
  ∀ (target : Type u) [Group target] [Finite target]
    (targetActor : Subgroup target) (targetSignalizer : target → Subgroup target),
    IsMulCommutative targetActor → (∀ member : targetActor, member ^ prime = 1) →
    Nat.card targetActor = prime ^ 3 → IsSolvableSignalizerFunctor prime targetActor targetSignalizer →
    Nat.card target + (signalizerSpectrum targetActor targetSignalizer).ncard <
      Nat.card G + (signalizerSpectrum actor signalizer).ncard →
    SignalizerComplete prime targetActor targetSignalizer

@[expose] def SignalizerLocallyComplete {G : Type u} [Group G]
    (prime : ℕ) (actor : Subgroup G) (signalizer : G → Subgroup G) : Prop :=
  (∀ subgroup : Subgroup G, SignalizerCompatible prime actor signalizer subgroup → subgroup ≠ ⊥ →
    SignalizerComplete prime (actor.subgroupOf (Subgroup.normalizer (subgroup : Set G)))
      (restrictedSignalizer (Subgroup.normalizer (subgroup : Set G)) signalizer)) ∧
  (∀ deleted ∈ signalizerSpectrum actor signalizer,
    SignalizerComplete prime actor
      (primeSetSignalizer (signalizerSpectrum actor signalizer \ {deleted}) actor signalizer))

theorem minimal_incomplete_normal_compatible_eq_bot {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hcomm : IsMulCommutative actor) (hpower : ∀ member : actor, member ^ prime = 1)
    (hcard : Nat.card actor = prime ^ 3) (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer)
    (hincomplete : ¬SignalizerComplete prime actor signalizer)
    (hminimal : SignalizerSizeMinimal prime actor signalizer)
    (kernel : Subgroup G) [kernel.Normal] (hcompatible : SignalizerCompatible prime actor signalizer kernel) :
    kernel = ⊥ := by
  by_contra hkernelNe
  have hpgroup : IsPGroup prime actor := IsPGroup.of_card hcard
  let quotient := QuotientGroup.mk' kernel
  have hinjective := quotient_actor_injOn_of_compatible_kernel prime hprime actor kernel signalizer hpgroup hcompatible
  have hquotientSmall := quotient_card_lt_of_nontrivial_subgroup kernel hkernelNe
  have hspectrumLe := Set.ncard_le_ncard
    (signalizerSpectrum_mapped_subset quotient actor signalizer hinjective)
    (signalizerSpectrum_finite actor signalizer)
  have hsize : Nat.card (G ⧸ kernel) +
      (signalizerSpectrum (actor.map quotient) (mappedSignalizer quotient actor signalizer)).ncard <
      Nat.card G + (signalizerSpectrum actor signalizer).ncard := by omega
  have hquotientCard : Nat.card (actor.map quotient) = prime ^ 3 :=
    (subgroup_card_map_of_injOn actor quotient hinjective).trans hcard
  have hcomplete := hminimal (G ⧸ kernel) (actor.map quotient) (mappedSignalizer quotient actor signalizer)
    (subgroup_map_commutative actor quotient hcomm) (subgroup_map_prime_power actor quotient prime hpower)
    hquotientCard (mappedSignalizer_isSolvableSignalizerFunctor prime hprime quotient actor signalizer
      hpgroup hinjective hsignalizer) hsize
  obtain ⟨plane, hplaneLe, hplaneCard, hplanePower⟩ :=
    exists_plane_in_rank_three_actor prime hprime actor hpower hcard
  exact hincomplete ((signalizer_complete_iff_quotient_complete prime hprime actor plane kernel signalizer
    hpgroup hplaneLe hplanePower
    hplaneCard hsignalizer hcompatible).mpr hcomplete)

theorem minimal_incomplete_compatible_normalizer_ne_top {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hcomm : IsMulCommutative actor) (hpower : ∀ member : actor, member ^ prime = 1)
    (hcard : Nat.card actor = prime ^ 3) (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer)
    (hincomplete : ¬SignalizerComplete prime actor signalizer)
    (hminimal : SignalizerSizeMinimal prime actor signalizer)
    (subgroup : Subgroup G) (hcompatible : SignalizerCompatible prime actor signalizer subgroup)
    (hne : subgroup ≠ ⊥) : Subgroup.normalizer (subgroup : Set G) ≠ ⊤ := by
  intro htop
  have : subgroup.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  exact hne (minimal_incomplete_normal_compatible_eq_bot prime hprime actor signalizer hcomm hpower hcard
    hsignalizer hincomplete hminimal subgroup hcompatible)

theorem minimal_incomplete_locally_complete {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hcomm : IsMulCommutative actor) (hpower : ∀ member : actor, member ^ prime = 1)
    (hcard : Nat.card actor = prime ^ 3) (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer)
    (hincomplete : ¬SignalizerComplete prime actor signalizer)
    (hminimal : SignalizerSizeMinimal prime actor signalizer) :
    SignalizerLocallyComplete prime actor signalizer := by
  constructor
  · intro subgroup hcompatible hne
    let normalizer := Subgroup.normalizer (subgroup : Set G)
    have hnormalizerNe : normalizer ≠ ⊤ := minimal_incomplete_compatible_normalizer_ne_top prime hprime
      actor signalizer hcomm hpower hcard hsignalizer hincomplete hminimal subgroup hcompatible hne
    have hsmall : Nat.card normalizer < Nat.card G := by
      have hstrict := subgroup_card_lt_of_lt normalizer ⊤ (lt_top_iff_ne_top.mpr hnormalizerNe)
      rw [Subgroup.card_top] at hstrict
      exact hstrict
    have hspectrumLe := Set.ncard_le_ncard (signalizerSpectrum_restriction_subset actor normalizer signalizer)
      (signalizerSpectrum_finite actor signalizer)
    have hsize : Nat.card normalizer +
        (signalizerSpectrum (actor.subgroupOf normalizer) (restrictedSignalizer normalizer signalizer)).ncard <
        Nat.card G + (signalizerSpectrum actor signalizer).ncard := by omega
    have hrestrictedComm : IsMulCommutative (actor.subgroupOf normalizer) := by
      apply isMulCommutative_iff.mpr
      intro first second
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun element : actor => (element : G))
        (isMulCommutative_iff.mp hcomm ⟨(first : normalizer), first.property⟩
          ⟨(second : normalizer), second.property⟩)
    have hrestrictedPower : ∀ member : actor.subgroupOf normalizer, member ^ prime = 1 := by
      intro member
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun element : actor => (element : G)) (hpower ⟨(member : normalizer), member.property⟩)
    have hrestrictedCard : Nat.card (actor.subgroupOf normalizer) = prime ^ 3 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcompatible.normalized).toEquiv).trans hcard
    exact hminimal normalizer (actor.subgroupOf normalizer) (restrictedSignalizer normalizer signalizer)
      hrestrictedComm hrestrictedPower hrestrictedCard
      (restrictedSignalizer_isSolvableSignalizerFunctor prime hprime actor normalizer signalizer hsignalizer) hsize
  · intro deleted hdeleted
    have hpgroup : IsPGroup prime actor := IsPGroup.of_card hcard
    have hsmall := prime_deleted_signalizerSpectrum_ncard_lt prime hprime actor signalizer hpgroup hsignalizer
      deleted hdeleted
    have hsize : Nat.card G + (signalizerSpectrum actor
        (primeSetSignalizer (signalizerSpectrum actor signalizer \ {deleted}) actor signalizer)).ncard <
        Nat.card G + (signalizerSpectrum actor signalizer).ncard := by omega
    exact hminimal G actor (primeSetSignalizer (signalizerSpectrum actor signalizer \ {deleted}) actor signalizer)
      hcomm hpower hcard (primeSetSignalizer_isSolvableSignalizerFunctor prime hprime
        (signalizerSpectrum actor signalizer \ {deleted}) actor signalizer hpgroup hcomm hsignalizer) hsize

end CFSG.RankThreeEvenClassification.Helpers
