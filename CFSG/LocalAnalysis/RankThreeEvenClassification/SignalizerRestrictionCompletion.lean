module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerSpectrum
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestriction

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem signalizerSpectrum_restriction_subset {G : Type u} [Group G] [Finite G]
    (actor overgroup : Subgroup G) (signalizer : G → Subgroup G) :
    signalizerSpectrum (actor.subgroupOf overgroup) (restrictedSignalizer overgroup signalizer) ⊆
      signalizerSpectrum actor signalizer := by
  rintro prime ⟨hprime, element, hmem, hne, hdiv⟩
  refine ⟨hprime, element, hmem, fun heq => hne (Subtype.ext heq), ?_⟩
  have hcard : Nat.card (restrictedSignalizer overgroup signalizer element) =
      Nat.card (signalizer element ⊓ overgroup : Subgroup G) :=
    (Subgroup.card_map_of_injective overgroup.subtype_injective).symm.trans
      (congrArg (fun subgroup : Subgroup G => Nat.card subgroup)
        (restrictedSignalizer_map_eq overgroup signalizer element))
  rw [hcard] at hdiv
  exact hdiv.trans (Subgroup.card_dvd_of_le inf_le_left)

theorem signalizerGenerated_restriction_map_eq {G : Type u} [Group G]
    (actor overgroup : Subgroup G) (signalizer : G → Subgroup G) (hactorLe : actor ≤ overgroup) :
    (signalizerGenerated (actor.subgroupOf overgroup) (restrictedSignalizer overgroup signalizer)).map
      overgroup.subtype =
        ⨆ (element : G) (_ : element ∈ actor) (_ : element ≠ 1), signalizer element ⊓ overgroup := by
  simp only [signalizerGenerated, Subgroup.map_iSup, restrictedSignalizer_map_eq]
  apply le_antisymm
  · apply iSup_le
    intro element
    apply iSup_le
    intro hmem
    apply iSup_le
    intro hne
    exact le_iSup_of_le (element : G) (le_iSup_of_le hmem
      (le_iSup_of_le (fun heq => hne (Subtype.ext heq)) le_rfl))
  · apply iSup_le
    intro element
    apply iSup_le
    intro hmem
    apply iSup_le
    intro hne
    exact le_iSup_of_le (⟨element, hactorLe hmem⟩ : overgroup) (le_iSup_of_le hmem
      (le_iSup_of_le (fun heq => hne (congrArg Subtype.val heq)) le_rfl))

theorem compatible_subgroup_le_restriction_completion
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor plane overgroup : Subgroup G)
    (signalizer : G → Subgroup G) (hactorLe : actor ≤ overgroup) (hplaneLe : plane ≤ actor)
    (hpower : ∀ member : plane, member ^ prime = 1) (hplaneCard : Nat.card plane = prime ^ 2)
    (subgroup : Subgroup G) (hcompatible : SignalizerCompatible prime actor signalizer subgroup)
    (hsubgroupLe : subgroup ≤ overgroup) :
    subgroup ≤ (signalizerGenerated (actor.subgroupOf overgroup)
      (restrictedSignalizer overgroup signalizer)).map overgroup.subtype := by
  rw [signalizerGenerated_restriction_map_eq actor overgroup signalizer hactorLe,
    solvable_centralizer_generation_of_plane prime hprime plane subgroup hpower hplaneCard
      hcompatible.solvable hcompatible.primeComplement (hplaneLe.trans hcompatible.normalized)]
  apply iSup_le
  intro member
  apply iSup_le
  intro hne
  have hmemberNe : (member : G) ≠ 1 := fun heq => hne (Subtype.ext heq)
  exact le_iSup_of_le (member : G) (le_iSup_of_le (hplaneLe member.property)
    (le_iSup_of_le hmemberNe (le_inf
      (hcompatible.fixed_le member (hplaneLe member.property) hmemberNe)
      (inf_le_left.trans hsubgroupLe))))

theorem SignalizerComplete.restriction {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor overgroup : Subgroup G) (signalizer : G → Subgroup G)
    (hactorLe : actor ≤ overgroup)
    (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer)
    (hcomplete : SignalizerComplete prime actor signalizer) :
    SignalizerComplete prime (actor.subgroupOf overgroup) (restrictedSignalizer overgroup signalizer) := by
  apply (signalizer_compatible_restriction_iff prime actor overgroup signalizer hactorLe _).mpr
  apply SignalizerCompatible.of_le prime actor signalizer (signalizerGenerated actor signalizer) _ hcomplete
  · rw [signalizerGenerated_restriction_map_eq actor overgroup signalizer hactorLe]
    apply iSup_le
    intro element
    apply iSup_le
    intro hmem
    apply iSup_le
    intro hne
    exact inf_le_left.trans (signalizer_value_le_generated actor signalizer element hmem hne)
  · have hrestricted := restrictedSignalizer_isSolvableSignalizerFunctor prime hprime
      actor overgroup signalizer hsignalizer
    have hnormalized := signalizerGenerated_normalized prime (actor.subgroupOf overgroup)
      (restrictedSignalizer overgroup signalizer) hrestricted
    apply Subgroup.le_normalizer_iff.mpr
    intro member hmember element helement
    obtain ⟨preimage, hpreimage, rfl⟩ := helement
    exact Subgroup.mem_map_of_mem overgroup.subtype
      (Subgroup.le_normalizer_iff.mp hnormalized ⟨member, hactorLe hmember⟩ hmember preimage hpreimage)

end CFSG.RankThreeEvenClassification.Helpers
