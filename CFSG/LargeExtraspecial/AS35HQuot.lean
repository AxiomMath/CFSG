module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LargeExtraspecial.AS35EBender
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

namespace CQuot

variable {G : Type} [Group G] (x : G)

abbrev Cx : Subgroup G := centralizer ({x} : Set G)

theorem self_mem_Cx : x ∈ Cx x := mem_centralizer_singleton_iff.mpr rfl

@[expose] def xC : Cx x := ⟨x, self_mem_Cx x⟩

@[simp] theorem coe_xC : ((xC x : Cx x) : G) = x := rfl

@[expose] def Nx : Subgroup (Cx x) where
  carrier := {c | c ∈ center (Cx x) ∧ Odd (orderOf c)}
  mul_mem' := by
    rintro a b ⟨ha, hao⟩ ⟨hb, hbo⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have hc : Commute a b := (mem_center_iff.mp hb a)
    exact Odd.of_dvd_nat (hao.mul hbo) (hc.orderOf_mul_dvd_lcm.trans
      (Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _)))
  one_mem' := ⟨one_mem _, by rw [orderOf_one]; decide⟩
  inv_mem' := by
    rintro a ⟨ha, hao⟩
    exact ⟨inv_mem ha, by rwa [orderOf_inv]⟩

theorem Nx_le_center : Nx x ≤ center (Cx x) := fun _ hc => hc.1

instance Nx_normal : (Nx x).Normal := Subgroup.normal_of_le_center (Nx_le_center x)

variable {x}

end CQuot

end CFSG.LargeExtraspecial
