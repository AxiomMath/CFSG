module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerSubgroups

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

@[expose] def restrictedSignalizer {G : Type u} [Group G]
    (overgroup : Subgroup G) (signalizer : G → Subgroup G) : overgroup → Subgroup overgroup :=
  fun element => (signalizer element).subgroupOf overgroup

theorem restrictedSignalizer_map_eq {G : Type u} [Group G]
    (overgroup : Subgroup G) (signalizer : G → Subgroup G) (element : overgroup) :
    (restrictedSignalizer overgroup signalizer element).map overgroup.subtype =
      signalizer element ⊓ overgroup :=
  Subgroup.subgroupOf_map_subtype _ _

theorem restrictedSignalizer_isSolvableSignalizerFunctor
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor overgroup : Subgroup G)
    (signalizer : G → Subgroup G) (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer) :
    IsSolvableSignalizerFunctor prime (actor.subgroupOf overgroup)
      (restrictedSignalizer overgroup signalizer) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro element hmem hne other hother
    have helementNe : (element : G) ≠ 1 := fun heq => hne (Subtype.ext heq)
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (hsignalizer.le_centralizer element hmem helementNe hother)
  · intro element hmem hne
    have helementNe : (element : G) ≠ 1 := fun heq => hne (Subtype.ext heq)
    apply hprime.coprime_iff_not_dvd.mpr
    intro hdiv
    apply hprime.coprime_iff_not_dvd.mp (hsignalizer.coprime element hmem helementNe)
    have hcard : Nat.card (restrictedSignalizer overgroup signalizer element) =
        Nat.card (signalizer element ⊓ overgroup : Subgroup G) :=
      (Subgroup.card_map_of_injective overgroup.subtype_injective).symm.trans
        (congrArg (fun subgroup : Subgroup G => Nat.card subgroup)
          (restrictedSignalizer_map_eq overgroup signalizer element))
    rw [hcard] at hdiv
    exact hdiv.trans (Subgroup.card_dvd_of_le inf_le_left)
  · intro element hmem hne conjugator hconjugator
    have helementNe : (element : G) ≠ 1 := fun heq => hne (Subtype.ext heq)
    apply Subgroup.map_injective overgroup.subtype_injective
    rw [Subgroup.map_map]
    have hcompose : overgroup.subtype.comp (MulAut.conj conjugator).toMonoidHom =
        (MulAut.conj (conjugator : G)).toMonoidHom.comp overgroup.subtype := by
      ext other
      rfl
    rw [hcompose, ← Subgroup.map_map, restrictedSignalizer_map_eq]
    rw [Subgroup.map_inf _ _ _ (MulAut.conj (conjugator : G)).injective,
      hsignalizer.invariant element hmem helementNe conjugator hconjugator]
    have hovergroupFixed : overgroup.map (MulAut.conj (conjugator : G)).toMonoidHom = overgroup :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer conjugator.property)
    rw [hovergroupFixed]
  · intro first hfirst hfirstNe second hsecond hsecondNe element helement
    have hfirstAmbientNe : (first : G) ≠ 1 := fun heq => hfirstNe (Subtype.ext heq)
    have hsecondAmbientNe : (second : G) ≠ 1 := fun heq => hsecondNe (Subtype.ext heq)
    apply hsignalizer.balance first hfirst hfirstAmbientNe second hsecond hsecondAmbientNe
    refine ⟨helement.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg (fun value : overgroup => (value : G))
      (Subgroup.mem_centralizer_singleton_iff.mp helement.2)
  · intro element hmem hne
    have helementNe : (element : G) ≠ 1 := fun heq => hne (Subtype.ext heq)
    have : Group.IsSolvable (signalizer element) := hsignalizer.solvable element hmem helementNe
    let embedding : restrictedSignalizer overgroup signalizer element →* signalizer element :=
      { toFun := fun other => ⟨other, other.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact Group.isSolvable_of_isSolvable_injective (f := embedding)
      (fun first second heq => by
        have hvalue : ((first : overgroup) : G) = ((second : overgroup) : G) :=
          congrArg (fun value : signalizer element => (value : G)) heq
        exact Subtype.ext (Subtype.ext hvalue))

theorem subgroup_map_subtype_inf_centralizer_singleton
    {G : Type u} [Group G] (overgroup : Subgroup G) (subgroup : Subgroup overgroup)
    (element : overgroup) :
    (subgroup ⊓ Subgroup.centralizer ({element} : Set overgroup)).map overgroup.subtype =
      subgroup.map overgroup.subtype ⊓ Subgroup.centralizer ({(element : G)} : Set G) := by
  ext other
  constructor
  · rintro ⟨preimage, hpreimage, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem overgroup.subtype hpreimage.1,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg (fun value : overgroup => (value : G))
      (Subgroup.mem_centralizer_singleton_iff.mp hpreimage.2)
  · rintro ⟨⟨preimage, hpreimage, rfl⟩, hcentralizer⟩
    refine ⟨preimage, ⟨hpreimage, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, rfl⟩
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp hcentralizer

theorem signalizer_compatible_restriction_iff
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (actor overgroup : Subgroup G) (signalizer : G → Subgroup G)
    (hactorLe : actor ≤ overgroup) (subgroup : Subgroup overgroup) :
    SignalizerCompatible prime (actor.subgroupOf overgroup)
        (restrictedSignalizer overgroup signalizer) subgroup ↔
      SignalizerCompatible prime actor signalizer (subgroup.map overgroup.subtype) := by
  have hcard : Nat.card (subgroup.map overgroup.subtype) = Nat.card subgroup :=
    Subgroup.card_map_of_injective overgroup.subtype_injective
  constructor
  · intro hcompatible
    have : Group.IsSolvable subgroup := hcompatible.solvable
    refine ⟨?_, Group.isSolvable_of_surjective (f := overgroup.subtype.subgroupMap subgroup)
      (overgroup.subtype.subgroupMap_surjective subgroup), hcard.symm ▸ hcompatible.primeComplement, ?_⟩
    · apply Subgroup.le_normalizer_iff.mpr
      intro member hmember element helement
      obtain ⟨preimage, hpreimage, rfl⟩ := helement
      exact Subgroup.mem_map_of_mem overgroup.subtype
        (Subgroup.le_normalizer_iff.mp hcompatible.normalized
          ⟨member, hactorLe hmember⟩ hmember preimage hpreimage)
    · intro element helement hne other hother
      obtain ⟨preimage, hpreimage, rfl⟩ := hother.1
      have hfixed : preimage ∈ Subgroup.centralizer ({⟨element, hactorLe helement⟩} : Set overgroup) := by
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        apply Subtype.ext
        exact Subgroup.mem_centralizer_singleton_iff.mp hother.2
      exact hcompatible.fixed_le ⟨element, hactorLe helement⟩ helement
        (fun heq => hne (congrArg Subtype.val heq)) ⟨hpreimage, hfixed⟩
  · intro hcompatible
    let equivalence := subgroup.equivMapOfInjective overgroup.subtype overgroup.subtype_injective
    have : Group.IsSolvable (subgroup.map overgroup.subtype) := hcompatible.solvable
    refine ⟨?_, Group.isSolvable_of_isSolvable_injective (f := equivalence.toMonoidHom)
      equivalence.injective, hcard ▸ hcompatible.primeComplement, ?_⟩
    · apply Subgroup.le_normalizer_iff.mpr
      intro member hmember element helement
      apply (Subgroup.mem_map_iff_mem overgroup.subtype_injective).mp
      exact Subgroup.le_normalizer_iff.mp hcompatible.normalized member hmember element
        (Subgroup.mem_map_of_mem overgroup.subtype helement)
    · intro element helement hne other hother
      have helementNe : (element : G) ≠ 1 := fun heq => hne (Subtype.ext heq)
      apply hcompatible.fixed_le element helement helementNe
      exact ⟨Subgroup.mem_map_of_mem overgroup.subtype hother.1,
        Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg (fun value : overgroup => (value : G))
            (Subgroup.mem_centralizer_singleton_iff.mp hother.2))⟩

end CFSG.RankThreeEvenClassification.Helpers
