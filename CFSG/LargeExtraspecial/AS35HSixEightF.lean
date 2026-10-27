module

public import CFSG.LargeExtraspecial.AS35HSixEightC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions CQuot

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem orderOf_rho_mul_eq_three {r t : G} (hrM : r ∈ S.M) (htM : t ∈ S.M)
    (h3 : orderOf (r * t) = 3) : orderOf (S.ρ ⟨r, hrM⟩ * S.ρ ⟨t, htM⟩) = 3 := by
  have h1 := S.orderOf_rhoL_eq_three (S.M.mul_mem hrM htM) h3
  rw [S.rhoL_mul_mem hrM htM] at h1
  rw [← h1, ← Subgroup.orderOf_coe]
  rfl

omit [Finite G] in
theorem not_orderOf_eq_three_of_commute {H : Type} [Group H] {α β : H} (hα : α * α = 1)
    (hβ : β * β = 1) (hc : α * β = β * α) : orderOf (α * β) ≠ 3 := by
  intro h
  have h2 : (α * β) ^ 2 = 1 := by
    rw [pow_two]
    calc α * β * (α * β) = α * (β * α) * β := by group
      _ = α * (α * β) * β := by rw [hc]
      _ = (α * α) * (β * β) := by group
      _ = 1 := by rw [hα, hβ, one_mul]
  have := orderOf_dvd_of_pow_eq_one h2
  rw [h] at this
  exact absurd this (by norm_num)

end Setting

end CFSG.LargeExtraspecial
