module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnPermDefs

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk5An

open Equiv Equiv.Perm CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23

theorem cycleType_replicate_of_sq {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α} (h : σ ^ 2 = 1) (k : ℕ)
    (hs : σ.support.card = 2 * k) : σ.cycleType = Multiset.replicate k 2 := by
  have h1 := Perm.cycleType_of_pow_prime_eq_one h
  have h2 := Perm.sum_cycleType σ
  rw [h1, Multiset.sum_replicate, smul_eq_mul, hs] at h2
  rw [h1]
  congr 1
  omega

theorem ct22 {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α} (h : σ ^ 2 = 1) (hs : σ.support.card = 4) :
    σ.cycleType = {2, 2} :=
  cycleType_replicate_of_sq h 2 hs

theorem ct2222 {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α} (h : σ ^ 2 = 1) (hs : σ.support.card = 8) :
    σ.cycleType = {2, 2, 2, 2} :=
  cycleType_replicate_of_sq h 4 hs

section Facts

variable (m : ℕ) (h7 : 7 ≤ m) (h10 : m ≤ 10)

include h7 h10

theorem sq_tb : tb m * tb m = 1 := by
  interval_cases m <;> decide

theorem sq_ub : ub m * ub m = 1 := by
  interval_cases m <;> decide

theorem sq_vb : vb m * vb m = 1 := by
  interval_cases m <;> decide

theorem sq_xb1 : xb1 m * xb1 m = 1 := by
  interval_cases m <;> decide

theorem sq_xb2 : xb2 m * xb2 m = 1 := by
  interval_cases m <;> decide

theorem sq_sg : sg m * sg m = 1 := by
  interval_cases m <;> decide

theorem ct_tb : (tb m).cycleType = {2, 2, 2, 2} := by
  exact ct2222 (by interval_cases m <;> decide) (by interval_cases m <;> decide)

theorem ct_ub : (ub m).cycleType = {2, 2, 2, 2} := by
  exact ct2222 (by interval_cases m <;> decide) (by interval_cases m <;> decide)

theorem ct_vb : (vb m).cycleType = {2, 2, 2, 2} := by
  exact ct2222 (by interval_cases m <;> decide) (by interval_cases m <;> decide)

theorem ct_xb1 : (xb1 m).cycleType = {2, 2, 2, 2} := by
  exact ct2222 (by interval_cases m <;> decide) (by interval_cases m <;> decide)

theorem ct_xb2 : (xb2 m).cycleType = {2, 2, 2, 2} := by
  exact ct2222 (by interval_cases m <;> decide) (by interval_cases m <;> decide)

theorem ct_ub_vb : (ub m * vb m).cycleType = {2, 2, 2, 2} := by
  exact ct2222 (by interval_cases m <;> decide) (by interval_cases m <;> decide)

theorem ct_xb1_xb2 : (xb1 m * xb2 m).cycleType = {2, 2, 2, 2} := by
  exact ct2222 (by interval_cases m <;> decide) (by interval_cases m <;> decide)

theorem ct_ub_xb2 : (ub m * xb2 m).cycleType = {2, 2} := by
  exact ct22 (by interval_cases m <;> decide) (by interval_cases m <;> decide)

theorem ct_vb_xb1 : (vb m * xb1 m).cycleType = {2, 2} := by
  exact ct22 (by interval_cases m <;> decide) (by interval_cases m <;> decide)

theorem ct_sg : (sg m).cycleType = {2, 2} := by
  exact ct22 (by interval_cases m <;> decide) (by interval_cases m <;> decide)

theorem ct_sg_tb : (sg m * tb m).cycleType = {2, 2, 2, 2} := by
  exact ct2222 (by interval_cases m <;> decide) (by interval_cases m <;> decide)

theorem ct_tb_ub : (tb m * ub m).cycleType = {2, 2, 2, 2} := by
  exact ct2222 (by interval_cases m <;> decide) (by interval_cases m <;> decide)

theorem comm_tb_ub : tb m * ub m = ub m * tb m := by
  interval_cases m <;> decide

theorem ct_tb_vb : (tb m * vb m).cycleType = {2, 2, 2, 2} := by
  exact ct2222 (by interval_cases m <;> decide) (by interval_cases m <;> decide)

theorem comm_tb_vb : tb m * vb m = vb m * tb m := by
  interval_cases m <;> decide

theorem ct_tb_xb1 : (tb m * xb1 m).cycleType = {2, 2, 2, 2} := by
  exact ct2222 (by interval_cases m <;> decide) (by interval_cases m <;> decide)

theorem comm_tb_xb1 : tb m * xb1 m = xb1 m * tb m := by
  interval_cases m <;> decide

theorem ct_tb_xb2 : (tb m * xb2 m).cycleType = {2, 2, 2, 2} := by
  exact ct2222 (by interval_cases m <;> decide) (by interval_cases m <;> decide)

theorem comm_tb_xb2 : tb m * xb2 m = xb2 m * tb m := by
  interval_cases m <;> decide

theorem comm_sg_tb : sg m * tb m = tb m * sg m := by
  interval_cases m <;> decide

theorem comm_ub_vb : ub m * vb m = vb m * ub m := by
  interval_cases m <;> decide

theorem comm_xb1_xb2 : xb1 m * xb2 m = xb2 m * xb1 m := by
  interval_cases m <;> decide

theorem comm_ub_xb2 : ub m * xb2 m = xb2 m * ub m := by
  interval_cases m <;> decide

theorem comm_vb_xb1 : vb m * xb1 m = xb1 m * vb m := by
  interval_cases m <;> decide

theorem comm_ub_xb1 : ub m * xb1 m * (ub m)⁻¹ * (xb1 m)⁻¹ = tb m := by
  interval_cases m <;> decide

theorem sg_ub : sg m * ub m * (sg m)⁻¹ = vb m := by
  interval_cases m <;> decide

theorem sg_xb1 : sg m * xb1 m * (sg m)⁻¹ = xb2 m := by
  interval_cases m <;> decide

theorem c3_cube : c3 m ^ 3 = 1 := by
  interval_cases m <;> decide

theorem c3_ne_one : c3 m ≠ 1 := by
  interval_cases m <;> decide

theorem comm_c3_tb : c3 m * tb m = tb m * c3 m := by
  interval_cases m <;> decide

end Facts

end CFSG.GH74.GLS.IVK.Proofs2.Ivk5An
