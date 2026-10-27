module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerSubgroups
public import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantCentralizerImages

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

noncomputable def mappedSignalizer {G : Type u} {H : Type v} [Group G] [Group H]
    (homomorphism : G →* H) (actor : Subgroup G) (signalizer : G → Subgroup G) : H → Subgroup H :=
  fun target => ⨆ (preimage : G) (_ : preimage ∈ actor) (_ : homomorphism preimage = target),
    (signalizer preimage).map homomorphism

theorem mappedSignalizer_apply_eq {G : Type u} {H : Type v} [Group G] [Group H]
    (homomorphism : G →* H) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hinjective : Set.InjOn homomorphism (actor : Set G))
    (element : G) (hmem : element ∈ actor) :
    mappedSignalizer homomorphism actor signalizer (homomorphism element) =
      (signalizer element).map homomorphism := by
  apply le_antisymm
  · apply iSup_le
    intro preimage
    apply iSup_le
    intro hpreimage
    apply iSup_le
    intro heq
    have hequal : preimage = element := hinjective hpreimage hmem heq
    rw [hequal]
  · exact le_iSup_of_le element (le_iSup_of_le hmem (le_iSup_of_le rfl le_rfl))

theorem map_conjugate_subgroup_eq {G : Type u} {H : Type v} [Group G] [Group H]
    (homomorphism : G →* H) (subgroup : Subgroup G) (element : G) :
    (subgroup.map (MulAut.conj element).toMonoidHom).map homomorphism =
      (subgroup.map homomorphism).map (MulAut.conj (homomorphism element)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext member
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

theorem mappedSignalizer_isSolvableSignalizerFunctor
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hpgroup : IsPGroup prime actor) (hinjective : Set.InjOn homomorphism (actor : Set G))
    (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer) :
    IsSolvableSignalizerFunctor prime (actor.map homomorphism)
      (mappedSignalizer homomorphism actor signalizer) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro element hmem hne
    obtain ⟨preimage, hpreimage, rfl⟩ := hmem
    have hpreimageNe : preimage ≠ 1 := fun heq => hne (heq ▸ map_one homomorphism)
    rw [mappedSignalizer_apply_eq homomorphism actor signalizer hinjective preimage hpreimage]
    rintro other ⟨representative, hrepresentative, rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    rw [← map_mul, ← map_mul]
    exact congrArg homomorphism (Subgroup.mem_centralizer_singleton_iff.mp
      (hsignalizer.le_centralizer preimage hpreimage hpreimageNe hrepresentative))
  · intro element hmem hne
    obtain ⟨preimage, hpreimage, rfl⟩ := hmem
    have hpreimageNe : preimage ≠ 1 := fun heq => hne (heq ▸ map_one homomorphism)
    rw [mappedSignalizer_apply_eq homomorphism actor signalizer hinjective preimage hpreimage]
    apply hprime.coprime_iff_not_dvd.mpr
    intro hdiv
    exact hprime.coprime_iff_not_dvd.mp (hsignalizer.coprime preimage hpreimage hpreimageNe)
      (hdiv.trans (Subgroup.card_map_dvd _ _))
  · intro element hmem hne member hmember
    obtain ⟨preimage, hpreimage, rfl⟩ := hmem
    obtain ⟨memberPreimage, hmemberPreimage, rfl⟩ := hmember
    have hpreimageNe : preimage ≠ 1 := fun heq => hne (heq ▸ map_one homomorphism)
    rw [mappedSignalizer_apply_eq homomorphism actor signalizer hinjective preimage hpreimage,
      ← map_conjugate_subgroup_eq, hsignalizer.invariant preimage hpreimage hpreimageNe
        memberPreimage hmemberPreimage]
  · intro first hfirst hfirstNe second hsecond hsecondNe
    obtain ⟨firstPreimage, hfirstPreimage, rfl⟩ := hfirst
    obtain ⟨secondPreimage, hsecondPreimage, rfl⟩ := hsecond
    have hfirstPreimageNe : firstPreimage ≠ 1 := fun heq => hfirstNe (heq ▸ map_one homomorphism)
    have hsecondPreimageNe : secondPreimage ≠ 1 := fun heq => hsecondNe (heq ▸ map_one homomorphism)
    rw [mappedSignalizer_apply_eq homomorphism actor signalizer hinjective firstPreimage hfirstPreimage,
      mappedSignalizer_apply_eq homomorphism actor signalizer hinjective secondPreimage hsecondPreimage]
    have hnormalized : actor ≤ Subgroup.normalizer (signalizer firstPreimage : Set G) := by
      intro member hmember
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
        (hsignalizer.invariant firstPreimage hfirstPreimage hfirstPreimageNe member hmember)
    rw [← normalized_prime_complement_singleton_centralizer_map_eq prime hprime homomorphism
      actor (signalizer firstPreimage) hpgroup
        (hprime.coprime_iff_not_dvd.mp (hsignalizer.coprime firstPreimage hfirstPreimage hfirstPreimageNe))
        hnormalized secondPreimage hsecondPreimage]
    exact Subgroup.map_mono
      (hsignalizer.balance firstPreimage hfirstPreimage hfirstPreimageNe
        secondPreimage hsecondPreimage hsecondPreimageNe)
  · intro element hmem hne
    obtain ⟨preimage, hpreimage, rfl⟩ := hmem
    have hpreimageNe : preimage ≠ 1 := fun heq => hne (heq ▸ map_one homomorphism)
    rw [mappedSignalizer_apply_eq homomorphism actor signalizer hinjective preimage hpreimage]
    have : Group.IsSolvable (signalizer preimage) := hsignalizer.solvable preimage hpreimage hpreimageNe
    exact Group.isSolvable_of_surjective (f := homomorphism.subgroupMap _)
      (homomorphism.subgroupMap_surjective _)

theorem SignalizerCompatible.map {G : Type u} {H : Type v} [Group G] [Group H] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (actor : Subgroup G) (signalizer : G → Subgroup G) (hpgroup : IsPGroup prime actor)
    (hinjective : Set.InjOn homomorphism (actor : Set G)) (subgroup : Subgroup G)
    (hcompatible : SignalizerCompatible prime actor signalizer subgroup) :
    SignalizerCompatible prime (actor.map homomorphism)
      (mappedSignalizer homomorphism actor signalizer) (subgroup.map homomorphism) := by
  have : Group.IsSolvable subgroup := hcompatible.solvable
  refine ⟨?_, Group.isSolvable_of_surjective (f := homomorphism.subgroupMap subgroup)
    (homomorphism.subgroupMap_surjective subgroup),
    fun hdiv => hcompatible.primeComplement (hdiv.trans (Subgroup.card_map_dvd _ _)), ?_⟩
  · apply Subgroup.le_normalizer_iff.mpr
    rintro member ⟨memberPreimage, hmemberPreimage, rfl⟩ element ⟨preimage, hpreimage, rfl⟩
    have hconjugate := Subgroup.le_normalizer_iff.mp hcompatible.normalized
      memberPreimage hmemberPreimage preimage hpreimage
    have hmapped := Subgroup.mem_map_of_mem homomorphism hconjugate
    simpa only [map_mul, map_inv] using hmapped
  · intro element helement hne
    obtain ⟨preimage, hpreimage, rfl⟩ := helement
    have hpreimageNe : preimage ≠ 1 := fun heq => hne (heq ▸ map_one homomorphism)
    rw [mappedSignalizer_apply_eq homomorphism actor signalizer hinjective preimage hpreimage,
      ← normalized_prime_complement_singleton_centralizer_map_eq prime hprime homomorphism
        actor subgroup hpgroup hcompatible.primeComplement hcompatible.normalized preimage hpreimage]
    exact Subgroup.map_mono (hcompatible.fixed_le preimage hpreimage hpreimageNe)

end CFSG.RankThreeEvenClassification.Helpers
