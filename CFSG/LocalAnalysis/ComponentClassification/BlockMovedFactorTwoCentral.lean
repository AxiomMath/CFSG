module

public import CFSG.LocalAnalysis.ComponentClassification.MovedCommutingFactorTwoCentral

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockMovedFactorTwoCentral

theorem central {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (first second : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (moving : G) (hmoving : moving ∈ first ⊓
      (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)
    (hmoved : (UniversalOrbitBlock.conjugate second actor).map (MulAut.conj moving).toMonoidHom ≠
      UniversalOrbitBlock.conjugate second actor)
    (acting : Subgroup G) (htwo : IsPGroup 2 acting)
    (hcontained : acting ≤ UniversalOrbitBlock.conjugate second actor)
    (hnormalizes : acting ≤ Subgroup.normalizer (first : Set G)) :
    acting ≤ (Subgroup.center (UniversalOrbitBlock.conjugate second actor)).map
      (UniversalOrbitBlock.conjugate second actor).subtype := by
  obtain ⟨original, horiginal, heq⟩ := Subgroup.mem_map.mp hmoving.2
  have hfactorOriginal := (UniversalOrbitBlock.normalizer_iff_preserves_block component heven huniversal hquasisimple
    original).mp horiginal second hsecond
  have himageEq : (UniversalOrbitBlock.conjugate second actor).map (MulAut.conj moving).toMonoidHom =
      UniversalOrbitBlock.conjugate (UniversalOrbitBlock.conjugate second original) actor := by
    change UniversalOrbitBlock.conjugate (UniversalOrbitBlock.conjugate second actor) moving = _
    rw [UniversalOrbitBlock.conjugate_conjugate, UniversalOrbitBlock.conjugate_conjugate]
    have hcommute : moving * actor = actor * original := by
      change actor * original * actor⁻¹ = moving at heq
      rw [← heq]
      group
    rw [hcommute]
  have hdistinct : second ≠ UniversalOrbitBlock.conjugate second original := by
    intro hequal
    exact hmoved (himageEq.trans (congrArg (fun factor => UniversalOrbitBlock.conjugate factor actor) hequal.symm))
  have hcommutes : ⁅UniversalOrbitBlock.conjugate second actor,
      (UniversalOrbitBlock.conjugate second actor).map (MulAut.conj moving).toMonoidHom⁆ = ⊥ := by
    rw [himageEq]
    have hmap := congrArg (Subgroup.map (MulAut.conj actor).toMonoidHom)
      (UniversalOrbitBlock.block_commutes component heven huniversal second hsecond
        (UniversalOrbitBlock.conjugate second original) hfactorOriginal hdistinct)
    change ⁅second.map (MulAut.conj actor).toMonoidHom,
      (UniversalOrbitBlock.conjugate second original).map (MulAut.conj actor).toMonoidHom⁆ = ⊥
    simpa only [Subgroup.map_commutator, Subgroup.map_bot] using hmap
  have hodd : Odd (Nat.card ↥(first ⊓ (UniversalOrbitBlock.conjugate second actor ⊔
      (UniversalOrbitBlock.conjugate second actor).map (MulAut.conj moving).toMonoidHom))) := by
    rw [himageEq]
    simpa only [sup_idem] using BlockProductFusion.intersection_odd component heven huniversal hquasisimple hcard
      first first second (UniversalOrbitBlock.conjugate second original) hfirst hfirst hsecond hfactorOriginal actor hactor
  exact MovedCommutingFactorTwoCentral.central first (UniversalOrbitBlock.conjugate second actor) acting htwo hcontained
    hnormalizes moving hmoving.1 hcommutes hodd

end CFSG.ComponentClassification.BlockMovedFactorTwoCentral
