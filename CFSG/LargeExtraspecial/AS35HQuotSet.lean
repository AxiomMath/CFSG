module

public import CFSG.LargeExtraspecial.AS35HQuot
public import CFSG.LargeExtraspecial.S3Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions CQuot

namespace Setting

variable {G : Type} [Group G] (S : Setting G)

section Quot

variable {x : G}

theorem pow_three_of_orderOf (hx3 : orderOf x = 3) : x ^ 3 = 1 := by
  rw [← hx3]
  exact pow_orderOf_eq_one x

theorem pow_four_of_mem_QG [Finite G] {y : G} (hy : y ∈ S.QG) : y ^ 4 = 1 := by
  rcases S.sq_eq_one_or_z hy with h | h
  · rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, one_pow]
  · rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, pow_two, S.z_mul_z]

variable [Finite G]

end Quot

end Setting

end CFSG.LargeExtraspecial
