module

public import CFSG.LocalAnalysis.ComponentClassification.ComponentFamilyPumpUpFusion
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.ThreePointCommutingActions
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationAction

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockThreeFactorImages

@[expose] noncomputable def image {G : Type*} [Group G] (normalizer factor : Subgroup G)
    (permutation : normalizer →* Equiv.Perm (Fin 3)) : Subgroup (Equiv.Perm (Fin 3)) :=
  (factor.subgroupOf normalizer).map permutation

theorem commute {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component)
    (normalizer : Subgroup G) (permutation : normalizer →* Equiv.Perm (Fin 3)) :
    Pairwise (fun first second : ↥(UniversalOrbitBlock.block component) =>
      ⁅image normalizer first.val permutation, image normalizer second.val permutation⁆ = ⊥) := by
  intro first second hne
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  rintro firstPermutation ⟨firstLift, hfirstLift, rfl⟩
  apply Subgroup.mem_centralizer_iff.mpr
  rintro secondPermutation ⟨secondLift, hsecondLift, rfl⟩
  rw [← map_mul, ← map_mul]
  apply congrArg permutation
  apply Subtype.ext
  have hcentral := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (UniversalOrbitBlock.block_commutes component heven huniversal first.val first.property second.val second.property
      (fun heq => hne (Subtype.ext heq)))
  exact Subgroup.mem_centralizer_iff.mp (hcentral hfirstLift) secondLift.val hsecondLift

theorem range_eq {G : Type*} [Group G] (normalizer factor : Subgroup G)
    (permutation : normalizer →* Equiv.Perm (Fin 3)) :
    let overlap := factor ⊓ normalizer
    let inclusion := Subgroup.inclusion (inf_le_right : overlap ≤ normalizer)
    (permutation.comp inclusion).range = image normalizer factor permutation := by
  ext member
  constructor
  · rintro ⟨lift, rfl⟩
    exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion inf_le_right lift, lift.property.1, rfl⟩
  · rintro ⟨lift, hlift, rfl⟩
    exact ⟨⟨lift.val, hlift, lift.property⟩, rfl⟩

theorem common_transposition {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (actor : G)
    (label : Fin 3 ≃ ↥(UniversalOrbitBlock.block (UniversalOrbitBlock.conjugate component actor)))
    (first second : Fin 3)
    (hevenOrbit : ∀ factor ∈ UniversalOrbitBlock.block component,
      Even (Nat.card ↥(ConjugationPairStabilizer.orbit
        (factor ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)
          (label first).val (label second).val))) :
    let conjugate := UniversalOrbitBlock.conjugate component actor
    let hevenConjugate := UniversalOrbitBlock.orbit_even component heven conjugate
      (UniversalOrbitBlock.orbit_conjugate component component (UniversalOrbitBlock.mem_orbit_self component) actor)
    let huniversalConjugate := UniversalOrbitBlock.orbit_universal component huniversal conjugate
      (UniversalOrbitBlock.orbit_conjugate component component (UniversalOrbitBlock.mem_orbit_self component) actor)
    let hquasisimpleConjugate := UniversalOrbitBlock.orbit_quasisimple component hquasisimple conjugate
      (UniversalOrbitBlock.orbit_conjugate component component (UniversalOrbitBlock.mem_orbit_self component) actor)
    let permutation := BlockPermutationAction.permutation conjugate hevenConjugate huniversalConjugate hquasisimpleConjugate label
    ∃ swap : Equiv.Perm (Fin 3),
      (swap = Equiv.swap 0 1 ∨ swap = Equiv.swap 0 2 ∨ swap = Equiv.swap 1 2) ∧
      ∀ factor ∈ UniversalOrbitBlock.block component, ∀ member : Equiv.Perm (Fin 3),
        member ∈ image (UniversalOrbitBlock.normalizer conjugate) factor permutation ↔ member = 1 ∨ member = swap := by
  classical
  let conjugate := UniversalOrbitBlock.conjugate component actor
  have horbit := UniversalOrbitBlock.orbit_conjugate component component (UniversalOrbitBlock.mem_orbit_self component) actor
  have hevenConjugate := UniversalOrbitBlock.orbit_even component heven conjugate horbit
  have huniversalConjugate := UniversalOrbitBlock.orbit_universal component huniversal conjugate horbit
  have hquasisimpleConjugate := UniversalOrbitBlock.orbit_quasisimple component hquasisimple conjugate horbit
  let permutation := BlockPermutationAction.permutation conjugate hevenConjugate huniversalConjugate hquasisimpleConjugate label
  let Index := ↥(UniversalOrbitBlock.block component)
  let subgroups : Index → Subgroup (Equiv.Perm (Fin 3)) :=
    fun factor => image (UniversalOrbitBlock.normalizer conjugate) factor.val permutation
  have hother : ∀ index : Index, ∃ other : Index, index ≠ other := by
    let : Fintype Index := Fintype.ofFinite Index
    have hfamilyCard : 3 ≤ Fintype.card Index := by simpa only [Nat.card_eq_fintype_card] using hcard
    intro index
    obtain ⟨other, hother, _⟩ := ComponentFamilyPumpUpFusion.exists_outside_two hfamilyCard index index
    exact ⟨other, hother.symm⟩
  have hevenImages : ∀ factor : Index, Even (Nat.card (subgroups factor)) := by
    intro factor
    let overlap := factor.val ⊓ UniversalOrbitBlock.normalizer conjugate
    have hcontained : overlap ≤ UniversalOrbitBlock.normalizer conjugate := inf_le_right
    have hcardOrbit := BlockPermutationAction.orbit_card conjugate hevenConjugate huniversalConjugate hquasisimpleConjugate
      label overlap hcontained first second
    have hevenOverlap : Even (Nat.card ↥(ConjugationPairStabilizer.orbit overlap (label first).val (label second).val)) := by
      have heven := hevenOrbit factor.val factor.property
      rwa [OrbitBlockConjugation.normalizer] at heven
    rw [hcardOrbit] at hevenOverlap
    have hevenImage := ThreePointCommutingActions.even_orbit_even_card _ ({first, second} : Set (Fin 3)) hevenOverlap
    rw [range_eq] at hevenImage
    exact hevenImage
  obtain ⟨swap, hswap, hcommon⟩ := ThreePointCommutingActions.common_swap subgroups hother
    (commute component heven huniversal (UniversalOrbitBlock.normalizer conjugate) permutation) hevenImages
      (⟨component, UniversalOrbitBlock.mem_block_self component⟩ : Index)
  exact ⟨swap, hswap, fun factor hfactor member => hcommon ⟨factor, hfactor⟩ member⟩

end CFSG.ComponentClassification.BlockThreeFactorImages
