module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnPermFacts1

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk5An

open Equiv Equiv.Perm

section VP

variable (m : ℕ) (h7 : 7 ≤ m) (h10 : m ≤ 10) (h9 : 9 ≤ m)

include h7 h10 h9

theorem sq_vp : vp m * vp m = 1 := by
  interval_cases m <;> first | omega | decide

theorem ct_vp : (vp m).cycleType = {2, 2, 2, 2} :=
  ct2222 (by interval_cases m <;> first | omega | decide) (by interval_cases m <;> first | omega | decide)

theorem comm_vp_tb : vp m * tb m = tb m * vp m := by
  interval_cases m <;> first | omega | decide

theorem ct_vp_tb : (vp m * tb m).cycleType = {2, 2, 2, 2} :=
  ct2222 (by interval_cases m <;> first | omega | decide) (by interval_cases m <;> first | omega | decide)

theorem vp_c3 : vp m * c3 m * (vp m)⁻¹ = (c3 m)⁻¹ := by
  interval_cases m <;> first | omega | decide

end VP

section O3

variable (m : ℕ) (h7 : 7 ≤ m) (h10 : m ≤ 10) (hm : m = 10)

include h7 h10 hm

theorem o3_cube : o3 m ^ 3 = 1 := by
  subst hm
  decide

theorem o3_ne_one : o3 m ≠ 1 := by
  subst hm
  decide

theorem comm_o3_ub : o3 m * ub m = ub m * o3 m := by
  subst hm
  decide

theorem comm_o3_vb : o3 m * vb m = vb m * o3 m := by
  subst hm
  decide

theorem comm_o3_xb1 : o3 m * xb1 m = xb1 m * o3 m := by
  subst hm
  decide

theorem comm_o3_xb2 : o3 m * xb2 m = xb2 m * o3 m := by
  subst hm
  decide

theorem comm_o3_tb : o3 m * tb m = tb m * o3 m := by
  subst hm
  decide

theorem comm_o3_c3 : o3 m * c3 m = c3 m * o3 m := by
  subst hm
  decide

theorem vp_o3 : vp m * o3 m * (vp m)⁻¹ = (o3 m)⁻¹ := by
  subst hm
  decide

end O3

end CFSG.GH74.GLS.IVK.Proofs2.Ivk5An
