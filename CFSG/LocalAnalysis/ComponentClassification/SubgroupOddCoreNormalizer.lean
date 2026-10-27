module

public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.Assembly.Defs

public section

open CFSG.Open

namespace CFSG.ComponentClassification.SubgroupOddCoreNormalizer

theorem inf {G : Type*} [Group G] (first second acting : Subgroup G)
    (hfirst : acting ≤ Subgroup.normalizer (first : Set G))
    (hsecond : acting ≤ Subgroup.normalizer (second : Set G)) :
    acting ≤ Subgroup.normalizer ((first ⊓ second : Subgroup G) : Set G) := by
  intro actor hactor
  apply Subgroup.mem_normalizer_iff.mpr
  intro member
  exact and_congr (Subgroup.mem_normalizer_iff.mp (hfirst hactor) member)
    (Subgroup.mem_normalizer_iff.mp (hsecond hactor) member)

theorem core {G : Type*} [Group G] (subgroup : Subgroup G) :
    Subgroup.normalizer (subgroup : Set G) ≤
      Subgroup.normalizer (((componentClassificationOddCore subgroup).map subgroup.subtype : Subgroup G) : Set G) := by
  have hconjugates : ∀ actor ∈ Subgroup.normalizer (subgroup : Set G), ∀ member,
      member ∈ (componentClassificationOddCore subgroup).map subgroup.subtype →
        actor * member * actor⁻¹ ∈ (componentClassificationOddCore subgroup).map subgroup.subtype := by
    intro actor hactor member hmember
    let automorphism := subgroup.normalizerMonoidHom ⟨actor, hactor⟩
    obtain ⟨lift, hlift, rfl⟩ := Subgroup.mem_map.mp hmember
    apply Subgroup.mem_map.mpr
    refine ⟨automorphism lift, ?_, rfl⟩
    rw [← OddCore.char_invariant automorphism]
    exact Subgroup.mem_map.mpr ⟨lift, hlift, rfl⟩
  intro actor hactor
  apply Subgroup.mem_normalizer_iff.mpr
  intro member
  constructor
  · exact hconjugates actor hactor member
  · intro hmember
    have hinverse := hconjugates actor⁻¹ ((Subgroup.normalizer _).inv_mem hactor)
      (actor * member * actor⁻¹) hmember
    convert hinverse using 1
    group

end CFSG.ComponentClassification.SubgroupOddCoreNormalizer
