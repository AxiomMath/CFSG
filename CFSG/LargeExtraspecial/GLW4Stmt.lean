module

public import CFSG.LargeExtraspecial.S14Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.LargeExtraspecial.S4

@[expose] def CentPlus6Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O),
    Stage S g t → Config.omegaPlus6.Occurs S g t → IsExtraspecialPGroup 2 (Nbar S g t) →
    IsSimpleGroup (Mbar0 S) → Concl14_7 S g t → Rbar S g t ≤ (Mbar0 S).map S.Mbar.subtype →
    FCt S t = Nbar S g t →
    (∃ x ∈ (Mbar0 S).map S.Mbar.subtype, x * t * x⁻¹ ∈ Nbar S g t ∧ x * t * x⁻¹ ≠ t) →
    ∀ k ∈ (Mbar0 S).map S.Mbar.subtype, k * t = t * k →
      ∃ r ∈ Rbar S g t, ∀ v ∈ Vt S g t, ((r⁻¹ * k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v

end CFSG.LargeExtraspecial.S14
