module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerSpectrum
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImages

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem signalizerSpectrum_mapped_subset {G : Type u} {H : Type v} [Group G] [Group H]
    (homomorphism : G →* H) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hinjective : Set.InjOn homomorphism (actor : Set G)) :
    signalizerSpectrum (actor.map homomorphism) (mappedSignalizer homomorphism actor signalizer) ⊆
      signalizerSpectrum actor signalizer := by
  rintro prime ⟨hprime, element, hmem, hne, hdiv⟩
  obtain ⟨preimage, hpreimage, rfl⟩ := hmem
  refine ⟨hprime, preimage, hpreimage, fun heq => hne (heq ▸ map_one homomorphism), ?_⟩
  rw [mappedSignalizer_apply_eq homomorphism actor signalizer hinjective preimage hpreimage] at hdiv
  exact hdiv.trans (Subgroup.card_map_dvd _ _)

theorem signalizerGenerated_map_eq {G : Type u} {H : Type v} [Group G] [Group H]
    (homomorphism : G →* H) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hinjective : Set.InjOn homomorphism (actor : Set G)) :
    (signalizerGenerated actor signalizer).map homomorphism =
      signalizerGenerated (actor.map homomorphism) (mappedSignalizer homomorphism actor signalizer) := by
  simp only [signalizerGenerated, Subgroup.map_iSup]
  apply le_antisymm
  · apply iSup_le
    intro element
    apply iSup_le
    intro hmem
    apply iSup_le
    intro hne
    have hmappedNe : homomorphism element ≠ 1 := by
      intro heq
      exact hne (hinjective hmem actor.one_mem (heq.trans (map_one homomorphism).symm))
    apply le_iSup_of_le (homomorphism element)
    apply le_iSup_of_le (Subgroup.mem_map_of_mem homomorphism hmem)
    apply le_iSup_of_le hmappedNe
    rw [mappedSignalizer_apply_eq homomorphism actor signalizer hinjective element hmem]
  · apply iSup_le
    intro element
    apply iSup_le
    intro hmem
    apply iSup_le
    intro hne
    obtain ⟨preimage, hpreimage, rfl⟩ := hmem
    have hpreimageNe : preimage ≠ 1 := fun heq => hne (heq ▸ map_one homomorphism)
    rw [mappedSignalizer_apply_eq homomorphism actor signalizer hinjective preimage hpreimage]
    exact le_iSup_of_le preimage (le_iSup_of_le hpreimage (le_iSup_of_le hpreimageNe le_rfl))

theorem SignalizerComplete.map {G : Type u} {H : Type v} [Group G] [Group H] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (actor : Subgroup G) (signalizer : G → Subgroup G) (hpgroup : IsPGroup prime actor)
    (hinjective : Set.InjOn homomorphism (actor : Set G))
    (hcomplete : SignalizerComplete prime actor signalizer) :
    SignalizerComplete prime (actor.map homomorphism) (mappedSignalizer homomorphism actor signalizer) := by
  have himage := SignalizerCompatible.map prime hprime homomorphism actor signalizer hpgroup
    hinjective (signalizerGenerated actor signalizer) hcomplete
  rw [signalizerGenerated_map_eq homomorphism actor signalizer hinjective] at himage
  exact himage

end CFSG.RankThreeEvenClassification.Helpers
