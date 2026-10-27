module

public import CFSG.ClassicalInvolution.Phan.PhanQ6Bwd
import CFSG.ClassicalInvolution.Phan.PhanP21Graph

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.PhanP
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.PhanG
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

section NotCol

variable {F : Type} [Field F] {ε : F}

theorem not_colP_rot (hε : ε ≠ 0) (s t : F) (hst : s ^ 2 + t ^ 2 / ε = 1)
    (z : NPair ε) : ¬ ColP ε z (z.rot hε s t hst) := by
  rintro ⟨-, -, h3⟩
  apply h3
  have e1 : B8 z.x z.x = 2 := by rw [B8_self, z.hx]; ring
  have e2 : B8 z.y z.y = 2 * ε := by rw [B8_self, z.hy]
  have p1 : B8 z.x (z.rot hε s t hst).x = 2 * s := by
    simp only [NPair.rot_x, B8_lin_right, e1, z.hxy]
    ring
  have p2 : B8 z.y (z.rot hε s t hst).x = -(2 * t) := by
    simp only [NPair.rot_x, B8_lin_right, B8_comm z.y z.x, z.hxy, e2]
    field_simp
    ring
  rw [p1, p2]
  linear_combination 4 * hst

end NotCol

section Dict

variable {p e : ℕ} [Fact p.Prime]

theorem adj_iff (M : StdModel p e) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (g h : spinGroup (quadPlus 4 (GaloisField p e))) :
    (ptGraph M.S).Adj (g : spinGroup (quadPlus 4 (GaloisField p e)) ⧸ parab M.S {1, 2, 3})
        (h : spinGroup (quadPlus 4 (GaloisField p e)) ⧸ parab M.S {1, 2, 3}) ↔
      ColP M.ε (g • z0 M.ε) (h • z0 M.ε) := by
  have hK := StdModel.card_K hq
  have h2 := two_ne_zero_gf hp2 e
  have hgh : ColP M.ε (g • z0 M.ε) (h • z0 M.ε) ↔ ColStd M.ε (g⁻¹ * h) := by
    unfold ColStd
    have e : h • z0 M.ε = g • ((g⁻¹ * h) • z0 M.ε) := by
      rw [← NPair.mul_smul', mul_inv_cancel_left]
    rw [e, colP_smul]
  rw [hgh]
  constructor
  · rintro ⟨hne, c, d, hc, hd, hadj⟩
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective d
    rw [ptMap_mk, QuotientGroup.eq] at hc hd
    rw [phanSystem_adj_mk] at hadj
    have hp1 : g⁻¹ * u ∈ parab M.S {1, 2, 3} := by
      have := inv_mem hc
      simpa using this
    have hnP : g⁻¹ * h ∉ parab M.S {1, 2, 3} := fun hP => hne (QuotientGroup.eq.2 hP)
    have hfac : g⁻¹ * h = (g⁻¹ * u) * (u⁻¹ * u') * (u'⁻¹ * h) := by group
    obtain ⟨t, ht, r, hr, hρ⟩ := exists_mul_of_mem_parab_zero hK hadj
    have ht' : t ∈ parab M.S {1, 2, 3} := torusSub_le_parab (S := M.S) {1, 2, 3} ht
    have hrP : r ∉ parab M.S {1, 2, 3} := by
      intro hrP
      apply hnP
      rw [hfac, hρ]
      exact mul_mem (mul_mem hp1 (mul_mem ht' hrP)) hd
    have hrcol := colStd_of_mem_range_zero M hp2 hq hr hrP
    obtain ⟨s2, t2, hst2, hrot2⟩ := exists_rot_of_mem_parab M hp2 hq hd
    obtain ⟨s1, t1, hst1, hrot1⟩ := exists_rot_of_mem_parab M hp2 hq (mul_mem hp1 ht')
    have : g⁻¹ * h = (g⁻¹ * u * t) * r * (u'⁻¹ * h) := by
      rw [hfac, hρ]
      group
    rw [this]
    exact (colStd_mul_right M.hε hrot2).2 ((colStd_mul_left M.hε hrot1).2 hrcol)
  · intro hcol
    obtain ⟨y, hy, ρ, hρ, z, hz, hyρz⟩ := exists_factor_of_colStd M hp2 hq hcol
    have hne : (g : spinGroup (quadPlus 4 (GaloisField p e)) ⧸ parab M.S {1, 2, 3}) ≠ h := by
      intro heq
      have hP : g⁻¹ * h ∈ parab M.S {1, 2, 3} := QuotientGroup.eq.1 heq
      obtain ⟨s, t, hst, hrot⟩ := exists_rot_of_mem_parab M hp2 hq hP
      unfold ColStd at hcol
      rw [hrot] at hcol
      exact not_colP_rot M.hε s t hst _ hcol
    exact ptGraph_adj_of_mul hy hρ hz hyρz hne

end Dict

end CFSG.ClassicalInvolution.PhanQ
