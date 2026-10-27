module

public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBTwoComponents
public import CFSG.LocalAnalysis.ComponentClassification.CentralTwoBInclusion

public section

namespace CFSG.ComponentClassification.AssemblyBLocalB

open AssemblyBPredicates AssemblyBTwoComponents

theorem localBProperty_iff_native (G : Type*) [Group G] :
    Assembly.ComponentType.LocalBProperty G ↔ LocalB.LocalBProperty G := by
  constructor
  · intro hlocalB twoSubgroup hnontrivial htwo component hcomponent
    exact (isComponentOf_iff_open component ⊤).mp
      (hlocalB twoSubgroup hnontrivial htwo component
        ((isTwoPComponent_iff_twoComponent component).mpr hcomponent))
  · intro hlocalB twoSubgroup hnontrivial htwo component hcomponent
    exact (isComponentOf_iff_open component ⊤).mpr
      (hlocalB twoSubgroup hnontrivial htwo component
        ((isTwoPComponent_iff_twoComponent component).mp hcomponent))

theorem of_corefree_and_inclusion {G : Type*} [Group G] [Finite G]
    (hcorefree : Assembly.oddCore G = ⊥) (hinclusion : CentralTwoBInclusion.Property G) :
    Assembly.ComponentType.LocalBProperty G :=
  (localBProperty_iff_native G).mpr
    (CentralTwoBInclusion.localB_of_corefree hcorefree hinclusion)

theorem ordinary_at_involution {G : Type*} [Group G] [Finite G]
    (hlocalB : Assembly.ComponentType.LocalBProperty G)
    (involution : G) (hinvolution : orderOf involution = 2)
    (component : Subgroup (Subgroup.centralizer ({involution} : Set G)))
    (hcomponent : Assembly.ComponentType.IsTwoPComponent component) :
    Assembly.IsComponentOf component ⊤ :=
  (isComponentOf_iff_open component ⊤).mpr
    (LocalB.ordinary_at_involution ((localBProperty_iff_native G).mp hlocalB)
      involution hinvolution component
      ((isTwoPComponent_iff_twoComponent component).mp hcomponent))

theorem hasInvolutionComponent_of_componentType {G : Type*} [Group G] [Finite G]
    (hlocalB : Assembly.ComponentType.LocalBProperty G)
    (hcomponentType : Assembly.IsComponentType G) : Open.HasInvolutionComponent G :=
  LocalB.hasInvolutionComponent_of_componentType
    ((localBProperty_iff_native G).mp hlocalB)
    ((isComponentType_iff_open G).mp hcomponentType)

end CFSG.ComponentClassification.AssemblyBLocalB
