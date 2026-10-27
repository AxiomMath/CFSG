module

public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockFusion

@[expose] def involutions {G : Type*} [Group G] (component : Subgroup G) : Set G :=
  {element | orderOf element = 2 ∧ ∃ factor ∈ UniversalOrbitBlock.block component,
    element ∈ Subgroup.centralizer (factor : Set G)}

theorem involution_mem_normalizer {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (element : G) (hmem : element ∈ involutions component) :
    element ∈ UniversalOrbitBlock.normalizer component := by
  obtain ⟨horder, factor, hfactor, hcentralizes⟩ := hmem
  exact UniversalOrbitBlock.involution_centralizer_le component heven huniversal hquasisimple factor hfactor
    element horder hcentralizes (Subgroup.mem_centralizer_singleton_iff.mpr rfl)

theorem nonempty {G : Type*} [Group G] [Finite G] (component : Subgroup G)
    (hcentralizer : Even (Nat.card (Subgroup.centralizer (component : Set G)))) :
    (involutions component).Nonempty := by
  have hdivides : 2 ∣ Nat.card (Subgroup.centralizer (component : Set G)) := by
    obtain ⟨half, hhalf⟩ := hcentralizer
    exact ⟨half, by omega⟩
  obtain ⟨element, horder⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer (component : Set G))
    2 hdivides
  exact ⟨element.val, (orderOf_injective _ (Subgroup.centralizer (component : Set G)).subtype_injective
    element).trans horder, component, UniversalOrbitBlock.mem_block_self component, element.property⟩

theorem image_mem {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (actor : G) (hactor : actor ∈ UniversalOrbitBlock.normalizer component)
    (element : G) (hmem : element ∈ involutions component) :
    (MulAut.conj actor) element ∈ involutions component := by
  obtain ⟨horder, factor, hfactor, hcentralizes⟩ := hmem
  have himage := (UniversalOrbitBlock.normalizer_iff_preserves_block component heven huniversal hquasisimple actor).mp
    hactor factor hfactor
  exact ⟨(orderOf_injective (MulAut.conj actor).toMonoidHom (MulAut.conj actor).injective element).trans horder,
    UniversalOrbitBlock.conjugate factor actor, himage,
    UniversalComponentBlock.centralizing_image (MulAut.conj actor) factor element hcentralizes⟩

theorem common_involution_forces_normalizer {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (first second : Subgroup G) (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component) (actor element : G)
    (horder : orderOf element = 2)
    (hfirstCentralizes : element ∈ Subgroup.centralizer (UniversalOrbitBlock.conjugate first actor : Set G))
    (hsecondCentralizes : element ∈ Subgroup.centralizer (second : Set G)) :
    actor ∈ UniversalOrbitBlock.normalizer component := by
  have horbit := UniversalOrbitBlock.orbit_conjugate component first hfirst.1 actor
  have himageLocal := UniversalOrbitBlock.orbit_universal component huniversal _ horbit element horder hfirstCentralizes
  have hsecondLocal := UniversalOrbitBlock.orbit_universal component huniversal second hsecond.1 element horder
    hsecondCentralizes
  have himageLe := UniversalComponentBlock.component_le_involution_centralizer _ element hfirstCentralizes
  have hsecondLe := UniversalComponentBlock.component_le_involution_centralizer second element hsecondCentralizes
  have hrelated : UniversalComponentBlock.Related (UniversalOrbitBlock.conjugate first actor) second := by
    by_cases heq : UniversalOrbitBlock.conjugate first actor = second
    · exact Or.inl heq
    · exact Or.inr (OrdinaryComponentTransport.commute_local_distinct _ _ _ himageLe hsecondLe
        himageLocal hsecondLocal heq)
  have himageBlock : UniversalOrbitBlock.conjugate first actor ∈ UniversalOrbitBlock.block component :=
    ⟨horbit, UniversalComponentBlock.related_trans _ second component
      (UniversalOrbitBlock.orbit_even component heven second hsecond.1)
      (UniversalOrbitBlock.orbit_universal component huniversal _ horbit) huniversal hrelated hsecond.2⟩
  exact UniversalOrbitBlock.normalizes_of_anchor_image component heven huniversal hquasisimple first hfirst actor himageBlock

theorem transporter_iff {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (element : G) (hmem : element ∈ involutions component) (actor : G) :
    (MulAut.conj actor) element ∈ involutions component ↔
      actor ∈ UniversalOrbitBlock.normalizer component := by
  constructor
  · rintro ⟨himageOrder, second, hsecond, hsecondCentralizes⟩
    obtain ⟨_, first, hfirst, hfirstCentralizes⟩ := hmem
    exact common_involution_forces_normalizer component heven huniversal hquasisimple first second hfirst hsecond
      actor ((MulAut.conj actor) element) himageOrder
      (UniversalComponentBlock.centralizing_image (MulAut.conj actor) first element hfirstCentralizes) hsecondCentralizes
  · intro hactor
    exact image_mem component heven huniversal hquasisimple actor hactor element hmem

theorem conjugate_intersection_iff {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcentralizer : Even (Nat.card (Subgroup.centralizer (component : Set G)))) (actor : G) :
    ((involutions component) ∩ (MulAut.conj actor) '' (involutions component)).Nonempty ↔
      actor ∈ UniversalOrbitBlock.normalizer component := by
  constructor
  · rintro ⟨_, hmem, element, helement, rfl⟩
    exact (transporter_iff component heven huniversal hquasisimple element helement actor).mp hmem
  · intro hactor
    obtain ⟨element, hmem⟩ := nonempty component hcentralizer
    exact ⟨(MulAut.conj actor) element, image_mem component heven huniversal hquasisimple actor hactor element hmem,
      element, hmem, rfl⟩

end CFSG.ComponentClassification.BlockFusion
