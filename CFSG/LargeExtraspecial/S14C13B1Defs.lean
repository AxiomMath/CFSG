module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LargeExtraspecial.S14Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.LargeExtraspecial.S4

@[expose] def Ybar13Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O),
    Stage S g t → Config.omegaPlus8b.Occurs S g t → IsExtraspecialPGroup 2 (Nbar S g t) →
      Concl14_7 S g t → FCt S t = Nbar S g t →
      ∀ α ∈ Ct S t, ∀ β ∈ Ct S t, α * α ∈ Nbar S g t → β * β ∈ Nbar S g t →
        α * β ∉ Nbar S g t → (α * β) ^ 3 ∈ Nbar S g t →
        (∀ r ∈ Rbar S g t, α * r * α⁻¹ * r⁻¹ ∈ Nbar S g t ∧ β * r * β⁻¹ * r⁻¹ ∈ Nbar S g t) →
        ∀ y ∈ Ct S t, y * α * y⁻¹ * α⁻¹ ∈ Nbar S g t → y * β * y⁻¹ * β⁻¹ ∈ Nbar S g t →
          y ∈ Rbar S g t

end CFSG.LargeExtraspecial.S14
