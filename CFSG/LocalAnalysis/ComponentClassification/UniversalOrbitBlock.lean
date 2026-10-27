module

public import CFSG.LocalAnalysis.ComponentClassification.UniversalComponentBlock
public import CFSG.LocalAnalysis.ComponentClassification.CommutingComponentFamily

public section

open CFSG.Open

namespace CFSG.ComponentClassification.UniversalOrbitBlock

@[expose] noncomputable def conjugate {G : Type*} [Group G] (component : Subgroup G) (actor : G) :
    Subgroup G := component.map (MulAut.conj actor).toMonoidHom

@[expose] def orbit {G : Type*} [Group G] (component : Subgroup G) : Set (Subgroup G) :=
  {factor | ∃ actor : G, factor = conjugate component actor}

@[expose] def block {G : Type*} [Group G] (component : Subgroup G) : Set (Subgroup G) :=
  {factor | factor ∈ orbit component ∧ UniversalComponentBlock.Related factor component}

@[expose] noncomputable def generated {G : Type*} [Group G] (component : Subgroup G) : Subgroup G :=
  CommutingComponentFamily.generated (block component)

@[expose] noncomputable def normalizer {G : Type*} [Group G] (component : Subgroup G) : Subgroup G :=
  Subgroup.normalizer (generated component : Set G)

theorem conjugate_one {G : Type*} [Group G] (component : Subgroup G) :
    conjugate component 1 = component := by
  have hhom : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext member
    change 1 * member * (1 : G)⁻¹ = member
    simp only [one_mul, inv_one, mul_one]
  unfold conjugate
  rw [hhom, Subgroup.map_id]

theorem conjugate_conjugate {G : Type*} [Group G]
    (component : Subgroup G) (first second : G) :
    conjugate (conjugate component first) second = conjugate component (second * first) := by
  have hhom : (MulAut.conj second).toMonoidHom.comp (MulAut.conj first).toMonoidHom =
      (MulAut.conj (second * first)).toMonoidHom := by
    ext member
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  unfold conjugate
  rw [Subgroup.map_map, hhom]

theorem mem_orbit_self {G : Type*} [Group G] (component : Subgroup G) :
    component ∈ orbit component := ⟨1, (conjugate_one component).symm⟩

theorem mem_block_self {G : Type*} [Group G] (component : Subgroup G) :
    component ∈ block component :=
  ⟨mem_orbit_self component, UniversalComponentBlock.related_refl component⟩

theorem orbit_conjugate {G : Type*} [Group G] (component factor : Subgroup G)
    (hfactor : factor ∈ orbit component) (actor : G) :
    conjugate factor actor ∈ orbit component := by
  obtain ⟨lift, rfl⟩ := hfactor
  exact ⟨actor * lift, conjugate_conjugate component lift actor⟩

theorem orbit_even {G : Type*} [Group G] (component : Subgroup G)
    (heven : Even (Nat.card component)) (factor : Subgroup G) (hfactor : factor ∈ orbit component) :
    Even (Nat.card factor) := by
  obtain ⟨actor, rfl⟩ := hfactor
  unfold conjugate
  rwa [Subgroup.card_map_of_injective (MulAut.conj actor).injective]

theorem orbit_quasisimple {G : Type*} [Group G] (component : Subgroup G)
    (hquasisimple : IsQuasisimple component) (factor : Subgroup G)
    (hfactor : factor ∈ orbit component) : IsQuasisimple factor := by
  obtain ⟨actor, rfl⟩ := hfactor
  exact Components.quasisimple_of_equiv
    (component.equivMapOfInjective (MulAut.conj actor).toMonoidHom
      (MulAut.conj actor).injective).symm hquasisimple

theorem orbit_universal {G : Type*} [Group G] (component : Subgroup G)
    (huniversal : UniversalComponentBlock.Universal component) (factor : Subgroup G)
    (hfactor : factor ∈ orbit component) : UniversalComponentBlock.Universal factor := by
  obtain ⟨actor, rfl⟩ := hfactor
  exact UniversalComponentBlock.universal_map (MulAut.conj actor) component huniversal

theorem block_related {G : Type*} [Group G] [Finite G] (component : Subgroup G)
    (heven : Even (Nat.card component)) (huniversal : UniversalComponentBlock.Universal component)
    (first second : Subgroup G) (hfirst : first ∈ block component) (hsecond : second ∈ block component) :
    UniversalComponentBlock.Related first second :=
  UniversalComponentBlock.related_trans first component second heven
    (orbit_universal component huniversal first hfirst.1)
    (orbit_universal component huniversal second hsecond.1) hfirst.2
    (UniversalComponentBlock.related_symm hsecond.2)

theorem block_commutes {G : Type*} [Group G] [Finite G] (component : Subgroup G)
    (heven : Even (Nat.card component)) (huniversal : UniversalComponentBlock.Universal component) :
    ∀ first ∈ block component, ∀ second ∈ block component, first ≠ second → ⁅first, second⁆ = ⊥ := by
  intro first hfirst second hsecond hne
  exact (block_related component heven huniversal first second hfirst hsecond).resolve_left hne

theorem generated_perfect {G : Type*} [Group G] (component : Subgroup G)
    (hquasisimple : IsQuasisimple component) : Group.IsPerfect (generated component) := by
  apply CommutingComponentFamily.perfect
  intro factor hfactor
  exact ⟨(orbit_quasisimple component hquasisimple factor hfactor.1).1⟩

theorem factor_normal {G : Type*} [Group G] [Finite G] (component : Subgroup G)
    (heven : Even (Nat.card component)) (huniversal : UniversalComponentBlock.Universal component)
    (factor : Subgroup G) (hfactor : factor ∈ block component) :
    (factor.subgroupOf (generated component)).Normal :=
  CommutingComponentFamily.factor_normal (block component)
    (block_commutes component heven huniversal) factor hfactor

theorem components_exact {G : Type*} [Group G] [Finite G] (component : Subgroup G)
    (heven : Even (Nat.card component)) (huniversal : UniversalComponentBlock.Universal component)
    (hquasisimple : IsQuasisimple component) (factor : Subgroup G)
    (hfactorLe : factor ≤ generated component) :
    IsComponentOf (factor.subgroupOf (generated component)) ⊤ ↔ factor ∈ block component :=
  CommutingComponentFamily.components_exact (block component)
    (block_commutes component heven huniversal)
    (fun factor hfactor => orbit_quasisimple component hquasisimple factor hfactor.1) factor hfactorLe

theorem factor_component_normalizer {G : Type*} [Group G] [Finite G] (component : Subgroup G)
    (heven : Even (Nat.card component)) (huniversal : UniversalComponentBlock.Universal component)
    (hquasisimple : IsQuasisimple component) (factor : Subgroup G) (hfactor : factor ∈ block component) :
    IsComponentOf (factor.subgroupOf (normalizer component)) ⊤ :=
  CommutingComponentFamily.factor_component_normalizer (block component)
    (block_commutes component heven huniversal)
    (fun factor hfactor => orbit_quasisimple component hquasisimple factor hfactor.1) factor hfactor

theorem normalizer_iff_preserves_block {G : Type*} [Group G] [Finite G] (component : Subgroup G)
    (heven : Even (Nat.card component)) (huniversal : UniversalComponentBlock.Universal component)
    (hquasisimple : IsQuasisimple component) (actor : G) :
    actor ∈ normalizer component ↔
      ∀ factor ∈ block component, conjugate factor actor ∈ block component :=
  CommutingComponentFamily.normalizer_iff_preserves_family (block component)
    (block_commutes component heven huniversal)
    (fun factor hfactor => orbit_quasisimple component hquasisimple factor hfactor.1) actor

theorem normalizes_of_anchor_image {G : Type*} [Group G] [Finite G] (component : Subgroup G)
    (heven : Even (Nat.card component)) (huniversal : UniversalComponentBlock.Universal component)
    (hquasisimple : IsQuasisimple component) (anchor : Subgroup G) (hanchor : anchor ∈ block component)
    (actor : G) (hanchorImage : conjugate anchor actor ∈ block component) :
    actor ∈ normalizer component := by
  apply (normalizer_iff_preserves_block component heven huniversal hquasisimple actor).mpr
  intro factor hfactor
  have horbit := orbit_conjugate component factor hfactor.1 actor
  refine ⟨horbit, ?_⟩
  have hrelated := block_related component heven huniversal factor anchor hfactor hanchor
  have himages := (UniversalComponentBlock.related_map_iff (MulAut.conj actor) factor anchor).mpr hrelated
  exact UniversalComponentBlock.related_trans (conjugate factor actor) (conjugate anchor actor)
    component (orbit_even component heven _ hanchorImage.1)
    (orbit_universal component huniversal _ horbit) huniversal himages hanchorImage.2

theorem factor_normalizer_le {G : Type*} [Group G] [Finite G] (component : Subgroup G)
    (heven : Even (Nat.card component)) (huniversal : UniversalComponentBlock.Universal component)
    (hquasisimple : IsQuasisimple component) (factor : Subgroup G) (hfactor : factor ∈ block component) :
    Subgroup.normalizer (factor : Set G) ≤ normalizer component := by
  intro actor hactor
  apply normalizes_of_anchor_image component heven huniversal hquasisimple factor hfactor actor
  have heq := (CommutingComponentFamily.normalizer_iff_conjugate_eq factor actor).mp hactor
  change factor.map (MulAut.conj actor).toMonoidHom ∈ block component
  rwa [heq]

theorem involution_centralizer_le {G : Type*} [Group G] [Finite G] (component : Subgroup G)
    (heven : Even (Nat.card component)) (huniversal : UniversalComponentBlock.Universal component)
    (hquasisimple : IsQuasisimple component) (factor : Subgroup G) (hfactor : factor ∈ block component)
    (involution : G) (horder : orderOf involution = 2)
    (hcentralizes : involution ∈ Subgroup.centralizer (factor : Set G)) :
    Subgroup.centralizer {involution} ≤ normalizer component := by
  intro actor hactor
  have hfactorUniversal := orbit_universal component huniversal factor hfactor.1
  have hfactorComponent := hfactorUniversal involution horder hcentralizes
  have hfixed : (MulAut.conj actor) involution = involution := by
    have hcommutes := Subgroup.mem_centralizer_singleton_iff.mp hactor
    change actor * involution * actor⁻¹ = involution
    rw [hcommutes, mul_assoc, mul_inv_cancel, mul_one]
  have hcentralizerMap : (Subgroup.centralizer {involution}).map (MulAut.conj actor).toMonoidHom =
      Subgroup.centralizer {involution} := by
    rw [UniversalComponentBlock.singleton_centralizer_map, hfixed]
  have himageComponent := OrdinaryComponentTransport.map_nested (MulAut.conj actor) factor
    (Subgroup.centralizer {involution}) hfactorComponent
  rw [hcentralizerMap] at himageComponent
  have hfactorLe := UniversalComponentBlock.component_le_involution_centralizer factor involution hcentralizes
  have himageLe := Subgroup.map_mono (f := (MulAut.conj actor).toMonoidHom) hfactorLe
  rw [hcentralizerMap] at himageLe
  have hrelated : UniversalComponentBlock.Related (conjugate factor actor) factor := by
    by_cases heq : conjugate factor actor = factor
    · exact Or.inl heq
    · exact Or.inr (OrdinaryComponentTransport.commute_local_distinct _ _ _ himageLe hfactorLe
        himageComponent hfactorComponent heq)
  have horbit := orbit_conjugate component factor hfactor.1 actor
  have hblock : conjugate factor actor ∈ block component :=
    ⟨horbit, UniversalComponentBlock.related_trans _ factor component
      (orbit_even component heven factor hfactor.1)
      (orbit_universal component huniversal _ horbit) huniversal hrelated hfactor.2⟩
  exact normalizes_of_anchor_image component heven huniversal hquasisimple factor hfactor actor hblock

theorem normalizer_proper {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ left right : G, left * right ≠ right * left) (component : Subgroup G)
    (heven : Even (Nat.card component)) (huniversal : UniversalComponentBlock.Universal component)
    (hquasisimple : IsQuasisimple component)
    (hcentralizer : Even (Nat.card (Subgroup.centralizer (component : Set G)))) :
    normalizer component ≠ ⊤ := by
  intro htop
  have hnormal : (generated component).Normal := Subgroup.normalizer_eq_top_iff.mp htop
  have hcomponentLe : component ≤ generated component :=
    CommutingComponentFamily.factor_le (block component) component (mem_block_self component)
  have hgeneratedNe : generated component ≠ ⊥ := by
    intro hbot
    have hcomponentBot := le_bot_iff.mp (hbot ▸ hcomponentLe)
    exact (component.nontrivial_iff_ne_bot.mp (Quasisimple.nontrivial hquasisimple)) hcomponentBot
  have hgeneratedTop : generated component = ⊤ := hnormal.eq_bot_or_eq_top.resolve_left hgeneratedNe
  have hcomponentNormalLocal := factor_normal component heven huniversal component (mem_block_self component)
  have hnormalizes : generated component ≤ Subgroup.normalizer (component : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hcomponentLe).mp hcomponentNormalLocal
  have hcomponentNormalizerTop : Subgroup.normalizer (component : Set G) = ⊤ := by
    apply top_unique
    rwa [hgeneratedTop] at hnormalizes
  have hcomponentNormal : component.Normal := Subgroup.normalizer_eq_top_iff.mp hcomponentNormalizerTop
  have hcomponentTop : component = ⊤ := hcomponentNormal.eq_bot_or_eq_top.resolve_left
    (component.nontrivial_iff_ne_bot.mp (Quasisimple.nontrivial hquasisimple))
  have hcenter := Helpers.center_eq_bot G hnonab
  have hcentralizerBot : Subgroup.centralizer (component : Set G) = ⊥ := by
    rw [hcomponentTop]
    simpa only [Subgroup.coe_top, Subgroup.centralizer_univ] using hcenter
  rw [hcentralizerBot, Subgroup.card_bot] at hcentralizer
  have hnot : ¬ Even (1 : ℕ) := by rw [Nat.even_iff]; decide
  exact hnot hcentralizer

end CFSG.ComponentClassification.UniversalOrbitBlock
