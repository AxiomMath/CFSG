module

public import CFSG.GroupTheory.AschbacherBlock
public import CFSG.GroupTheory.FusionFamilyControl

public section

namespace CFSG.GroupTheory

@[expose] def McBrideGomi : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → CFSG.Open.IsKProper G →
    CFSG.Open.IsCharTwoType G →
    (∀ N : Subgroup G, CFSG.Open.IsMaxTwoLocalSubgroup N → ∀ B : Subgroup ↥N,
      ¬ IsAschbacherBlockGomi B) →
    ∀ T : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ →
      FamilyControlsFusion (charNormalizers T) T

end CFSG.GroupTheory

end
