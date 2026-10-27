module

public import CFSG.ClassicalInvolution.Uniform.UFacade
public import CFSG.ClassicalInvolution.Uniform.USat
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

theorem isClassicalMember3_sat {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}
    (h : IsClassicalMember3 K z) :
    IsClassicalMember3 (K ⊔ Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G))) z := by
  have h1 := (Uniform.IsClassicalMemberU.ofQ3 h).satU_member
  rw [Uniform.satU_of_isSolvableType
    (Uniform.MemberType.isSolvableType_sl2 (p := 3) (f := 1) |>.mpr (by norm_num))] at h1
  exact h1.toQ3 (by norm_num)

end CFSG.ClassicalInvolution.Q3
