module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates

public section

namespace CFSG.ComponentClassification.AssemblyBTwoComponents

open AssemblyBPredicates

theorem isTwoPComponent_iff_twoComponent {G : Type*} [Group G] (component : Subgroup G) :
    Assembly.ComponentType.IsTwoPComponent component ↔
      TwoComponents.IsTwoComponent component := by
  constructor
  · rintro ⟨image, himage, hchain, hmap, hminimal⟩
    refine ⟨(isSubnormal_iff_open component ⊤).mp hchain, ?_, ?_⟩
    · have hmap' : component.map
          (QuotientGroup.mk' (Open.componentClassificationOddCore G)) = image := hmap
      rw [hmap']
      exact (isComponentOf_iff_open image ⊤).mp himage
    · intro smaller hle hsmaller hsmallerMap
      by_contra hne
      have hlt : smaller < component := lt_of_le_of_ne hle hne
      apply hminimal smaller hlt ((isSubnormal_iff_open smaller ⊤).mpr hsmaller)
      exact hsmallerMap.trans hmap
  · rintro ⟨hchain, himage, hminimal⟩
    refine ⟨component.map (QuotientGroup.mk' (Assembly.oddCore G)),
      (isComponentOf_iff_open _ ⊤).mpr himage,
      (isSubnormal_iff_open component ⊤).mpr hchain, rfl, ?_⟩
    intro smaller hlt hsmaller hsmallerMap
    exact hlt.ne (hminimal smaller hlt.le
      ((isSubnormal_iff_open smaller ⊤).mp hsmaller) hsmallerMap)

theorem exists_lift {G : Type*} [Group G] [Finite G]
    (image : Subgroup (G ⧸ Assembly.oddCore G))
    (himage : Assembly.IsComponentOf image ⊤) :
    ∃ component : Subgroup G, Assembly.ComponentType.IsTwoPComponent component ∧
      component.map (QuotientGroup.mk' (Assembly.oddCore G)) = image := by
  obtain ⟨component, hcomponent, hmap⟩ :=
    TwoComponents.exists_lift image ((isComponentOf_iff_open image ⊤).mp himage)
  exact ⟨component, (isTwoPComponent_iff_twoComponent component).mpr hcomponent, hmap⟩

theorem perfect {G : Type*} [Group G] {component : Subgroup G}
    (hcomponent : Assembly.ComponentType.IsTwoPComponent component) :
    commutator component = ⊤ :=
  TwoComponents.perfect ((isTwoPComponent_iff_twoComponent component).mp hcomponent)

theorem quasisimple_quotient {G : Type*} [Group G] [Finite G] {component : Subgroup G}
    (hcomponent : Assembly.ComponentType.IsTwoPComponent component) :
    Assembly.IsQuasisimple (component ⧸ Assembly.oddCore component) :=
  (isQuasisimple_iff_open _).mpr
    (TwoComponents.quasisimple_quotient
      ((isTwoPComponent_iff_twoComponent component).mp hcomponent))

theorem isTwoPComponent_iff_residual_quasisimple {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) :
    Assembly.ComponentType.IsTwoPComponent component ↔
      Assembly.IsSubnormal component ⊤ ∧ TwoResidual.subgroup component = ⊤ ∧
        Assembly.IsQuasisimple (component ⧸ Assembly.oddCore component) := by
  rw [isTwoPComponent_iff_twoComponent, TwoComponentConvention.twoComponent_iff]
  rw [isSubnormal_iff_open, isQuasisimple_iff_open]
  rfl

theorem ordinary_of_corefree {G : Type*} [Group G] [Finite G]
    (hcorefree : Assembly.oddCore G = ⊥) {component : Subgroup G}
    (hcomponent : Assembly.ComponentType.IsTwoPComponent component) :
    Assembly.IsComponentOf component ⊤ :=
  (isComponentOf_iff_open component ⊤).mpr
    (TwoComponents.ordinary_of_corefree hcorefree
      ((isTwoPComponent_iff_twoComponent component).mp hcomponent))

end CFSG.ComponentClassification.AssemblyBTwoComponents
