module

public import CFSG.ClassicalInvolution.Q3.Q3ZAHeisPres
public import CFSG.ClassicalInvolution.Q3.Q3ZACalc
public import CFSG.ClassicalInvolution.Q3.Q3ZAHeisDatum
public import CFSG.ClassicalInvolution.Q3.Q3ZACrossModel

public section

namespace CFSG.ClassicalInvolution.Q3.Q3ZB

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.ClassicalInvolution.Q3.Q3ZA
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups
open Matrix

theorem rigid (S : StatedSp 2 F3) (h3 : S * S * S = 1)
    (hz : longInv F3 2 0 * S * longInv F3 2 0 = S⁻¹)
    (h1 : S * longBlock F3 2 0 uSL = longBlock F3 2 0 uSL * S)
    (h2 : S * longBlock F3 2 1 lSL = longBlock F3 2 1 lSL * S) :
    S = 1 ∨ S = sb uSL ∨ S = (sb uSL)⁻¹ := by
  have e1 := congrArg (mat 2 F3) h1
  rw [map_mul, map_mul, mat_longBlock] at e1
  have e2 := congrArg (mat 2 F3) h2
  rw [map_mul, map_mul, mat_longBlock] at e2
  have z1 := congrFun (congrFun e1 (Sum.inl 1)) (Sum.inr 0)
  have z2 := congrFun (congrFun e1 (Sum.inr 0)) (Sum.inr 0)
  have z3 := congrFun (congrFun e1 (Sum.inr 1)) (Sum.inr 0)
  have z4 := congrFun (congrFun e1 (Sum.inl 0)) (Sum.inl 1)
  have z5 := congrFun (congrFun e1 (Sum.inl 0)) (Sum.inr 1)
  have z6 := congrFun (congrFun e2 (Sum.inl 0)) (Sum.inl 1)
  have z7 := congrFun (congrFun e2 (Sum.inl 1)) (Sum.inl 1)
  have z8 := congrFun (congrFun e2 (Sum.inr 1)) (Sum.inr 0)
  have q1 := congrFun (congrFun e1 (Sum.inl 0)) (Sum.inr 0)
  have q2 := congrFun (congrFun e2 (Sum.inr 1)) (Sum.inl 1)
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
    CFSG.LieType.Steinberg.Sp.blockMat, uSL, lSL] at z1 z2 z3 z4 z5 z6 z7 z8 q1 q2
  have q1' : mat 2 F3 S (Sum.inr 0) (Sum.inr 0) = mat 2 F3 S (Sum.inl 0) (Sum.inl 0) := by
    linear_combination -q1
  have q2' : mat 2 F3 S (Sum.inr 1) (Sum.inr 1) = mat 2 F3 S (Sum.inl 1) (Sum.inl 1) := by
    linear_combination q2
  have s1 := form_mulVec S bE0 bF0
  have s2 := form_mulVec S bE1 bF1
  have s3 := form_mulVec S bE1 bF0
  simp [form_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Pi.single_apply, sgn, par] at s1 s2 s3
  simp only [z1, z2, z3, z4, z5, z6, z7, z8, q1', q2', mul_zero, zero_mul, add_zero, zero_add,
    neg_zero] at s1 s2 s3
  have t0 := congrFun (congrFun (congrArg (mat 2 F3) h3) (Sum.inl 0)) (Sum.inl 0)
  have t1 := congrFun (congrFun (congrArg (mat 2 F3) h3) (Sum.inl 1)) (Sum.inl 1)
  simp only [map_mul, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, z1, z2, z3, z4,
    z5, z6, z7, z8, q1', mul_zero, zero_mul, add_zero, zero_add, map_one,
    Matrix.one_apply_eq] at t0 t1
  have hzS : longInv F3 2 0 * S * longInv F3 2 0 * S = 1 := by rw [hz]; exact inv_mul_cancel S
  have u0 := congrFun (congrFun (congrArg (mat 2 F3) hzS) (Sum.inl 0)) (Sum.inr 0)
  have u1 := congrFun (congrFun (congrArg (mat 2 F3) hzS) (Sum.inr 1)) (Sum.inl 1)
  simp [map_mul, mat_longInv, Matrix.mul_apply, Matrix.diagonal_apply, Fintype.sum_sum_type,
    Fin.sum_univ_two, coords] at u0 u1
  simp only [z3, z4, z6, z8, q1', q2', mul_zero, zero_mul, add_zero, zero_add,
    neg_zero] at u0 u1
  have hl : mat 2 F3 S (Sum.inl 0) (Sum.inl 0) = 1 := by
    linear_combination (-(mat 2 F3 S (Sum.inl 0) (Sum.inl 0))) * s1 + t0
  have hm : mat 2 F3 S (Sum.inl 1) (Sum.inl 1) = 1 := by
    linear_combination (-(mat 2 F3 S (Sum.inl 1) (Sum.inl 1))) * s2 + t1
  have hb : mat 2 F3 S (Sum.inl 0) (Sum.inr 0) = 0 := by
    rw [hl] at u0
    linear_combination (mat 2 F3 S (Sum.inl 0) (Sum.inr 0)) * three_eq_zero_f3 - u0
  have hc : mat 2 F3 S (Sum.inr 1) (Sum.inl 1) = 0 := by
    rw [hm] at u1
    linear_combination (mat 2 F3 S (Sum.inr 1) (Sum.inl 1)) * three_eq_zero_f3 - u1
  have hd : mat 2 F3 S (Sum.inr 1) (Sum.inr 0) = -mat 2 F3 S (Sum.inl 0) (Sum.inl 1) := by
    rw [hl, hm] at s3
    linear_combination s3
  have key : S = sb (usl (mat 2 F3 S (Sum.inl 0) (Sum.inl 1))) := by
    refine eq_of_mulVec_basis ?_ ?_ ?_ ?_
    · rw [sb_usl_e0]
      funext r
      rw [mulVec_single_one_apply]
      rcases r with r | r <;> fin_cases r <;> simp [hl, z1, z2, z3]
    · rw [sb_usl_e1]
      funext r
      rw [mulVec_single_one_apply]
      rcases r with r | r <;> fin_cases r <;> simp [hm, hc, z4]
    · rw [sb_usl_f0]
      funext r
      rw [mulVec_single_one_apply]
      rcases r with r | r <;> fin_cases r <;> simp [hl, hb, hd, z8, q1', sub_eq_add_neg]
    · rw [sb_usl_f1]
      funext r
      rw [mulVec_single_one_apply]
      rcases r with r | r <;> fin_cases r <;> simp [hm, z5, z6, z7, q2']
  rcases eq_zero_or_one_or_neg_one_f3 (mat 2 F3 S (Sum.inl 0) (Sum.inl 1)) with h | h | h
  · left
    rw [key, h, usl_zero, map_one]
  · right; left
    rw [key, h, usl_one]
  · right; right
    rw [key, h, show (-1 : F3) = -1 from rfl, ← usl_inv, usl_one, map_inv]

open CFSG.ClassicalInvolution.Q3.Q3Z (negOne negOne_mem_center negOne_two_eq longInv_mul_self)

theorem longInv_inv (k : Fin 2) : (longInv F3 2 k)⁻¹ = longInv F3 2 k :=
  inv_eq_of_mul_eq_one_right (longInv_mul_self k)

theorem longInv0_sbU : longInv F3 2 0 * sbU * longInv F3 2 0 = sbU⁻¹ := by
  have h := iota_sb_usl 1
  rw [iota_apply, longInv_inv] at h
  rw [sbU_eq, sb_usl_inv]
  exact h

theorem conj_longInv1 (x : StatedSp 2 F3) :
    longInv F3 2 1 * x * (longInv F3 2 1)⁻¹ = longInv F3 2 0 * x * (longInv F3 2 0)⁻¹ := by
  have hc : negOne 2 F3 = longInv F3 2 0 * longInv F3 2 1 := negOne_two_eq
  have h1 : longInv F3 2 1 = longInv F3 2 0 * negOne 2 F3 := by
    rw [hc, ← mul_assoc, longInv_mul_self, one_mul]
  have hcen := Subgroup.mem_center_iff.1 (negOne_mem_center (n := 2) (F := F3))
  rw [h1, _root_.mul_inv_rev, longInv_inv]
  calc longInv F3 2 0 * negOne 2 F3 * x * ((negOne 2 F3)⁻¹ * longInv F3 2 0)
      = longInv F3 2 0 * (negOne 2 F3 * x * (negOne 2 F3)⁻¹) * longInv F3 2 0 := by group
    _ = longInv F3 2 0 * x * longInv F3 2 0 := by
        rw [← hcen x]; group

theorem sbU_ne_one : sbU ≠ 1 := by
  intro h
  have := congrArg (fun g => mat 2 F3 g *ᵥ bE1) h
  simp only [sbU_eq, sb_usl_e1, map_one, Matrix.one_mulVec] at this
  have h2 := congrFun this (Sum.inl 0)
  simp at h2

theorem hom_ext_H_sbU {Y : Type*} [Group Y] {ψ₁ ψ₂ : StatedSp 2 F3 →* Y}
    (h0 : ∀ x, ψ₁ (longBlock F3 2 0 x) = ψ₂ (longBlock F3 2 0 x))
    (h1 : ∀ x, ψ₁ (longBlock F3 2 1 x) = ψ₂ (longBlock F3 2 1 x))
    (hs : ψ₁ sbU = ψ₂ sbU) : ψ₁ = ψ₂ := by
  have hL : ψ₁ sbL = ψ₂ sbL := by
    have hL' : ψ₁ (sbL⁻¹) = ψ₂ (sbL⁻¹) := by
      rw [← weyl₀_conj]
      simp only [map_mul, map_inv, weyl₀, weyl₁, h0, h1, hs]
    simpa [map_inv] using hL'
  have htop : MonoidHom.eqLocus ψ₁ ψ₂ = ⊤ := by
    rw [eq_top_iff, ← sp4Gens_closure, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl | rfl)
    · exact hs
    · exact hL
    · exact h1 uSL
    · exact h1 lSL
  exact MonoidHom.ext fun x => (htop ▸ Subgroup.mem_top x : x ∈ MonoidHom.eqLocus ψ₁ ψ₂)

theorem longInv_comm_lb (k : Fin 2) (x : SL(2, F3)) :
    longInv F3 2 k * longBlock F3 2 k x = longBlock F3 2 k x * longInv F3 2 k := by
  rw [longInv, ← map_mul, ← map_mul, neg_mul, mul_neg, one_mul, mul_one]

theorem longInv0_comm_lb1 (x : SL(2, F3)) :
    longInv F3 2 0 * longBlock F3 2 1 x = longBlock F3 2 1 x * longInv F3 2 0 :=
  CFSG.ClassicalInvolution.Q3.Q3Z.commutes_planeGroup_stdPlane _
    (by rw [planeGroup_stdPlane]; exact ⟨-1, rfl⟩) _ (by rw [planeGroup_stdPlane]; exact ⟨x, rfl⟩)

theorem eq_or_conj_longInv {G : Type*} [Group G] (ψ : StatedSp 2 F3 →* G)
    (hψ : Function.Injective ψ) (b : G) (hb : ∀ g, ∃ g', b * ψ g * b⁻¹ = ψ g')
    (h0 : ∀ x, b * ψ (longBlock F3 2 0 x) * b⁻¹ = ψ (longBlock F3 2 0 x))
    (h1 : ∀ x, b * ψ (longBlock F3 2 1 x) * b⁻¹ = ψ (longBlock F3 2 1 x)) :
    (∀ g, b * ψ g * b⁻¹ = ψ g) ∨
      (∀ g, b * ψ g * b⁻¹ = ψ (longInv F3 2 0 * g * (longInv F3 2 0)⁻¹)) := by
  let c : StatedSp 2 F3 →* G := (MulAut.conj b).toMonoidHom.comp ψ
  have hc : ∀ g, c g = b * ψ g * b⁻¹ := fun g => rfl
  have hc0 : ∀ x, c (longBlock F3 2 0 x) = ψ (longBlock F3 2 0 x) := fun x => (hc _).trans (h0 x)
  have hc1 : ∀ x, c (longBlock F3 2 1 x) = ψ (longBlock F3 2 1 x) := fun x => (hc _).trans (h1 x)
  obtain ⟨S, hS⟩ := hb sbU
  have hcS : c sbU = ψ S := (hc _).trans hS
  have hS3 : S * S * S = 1 := by
    apply hψ
    rw [map_mul, map_mul, ← hcS, ← map_mul, ← map_mul, (pow_three' sbU).symm.trans sbU_pow_three,
      map_one, map_one]
  have hSz : longInv F3 2 0 * S * longInv F3 2 0 = S⁻¹ := by
    apply hψ
    rw [map_mul, map_mul, map_inv, ← hcS]
    have hz : ψ (longInv F3 2 0) = c (longInv F3 2 0) := (hc0 (-1)).symm
    rw [hz, ← map_mul, ← map_mul, longInv0_sbU, map_inv]
  have hS1 : S * longBlock F3 2 0 uSL = longBlock F3 2 0 uSL * S := by
    apply hψ
    rw [map_mul, map_mul, ← hcS, ← hc0 uSL, ← map_mul, ← map_mul, ← M4]
  have hS2 : S * longBlock F3 2 1 lSL = longBlock F3 2 1 lSL * S := by
    apply hψ
    rw [map_mul, map_mul, ← hcS, ← hc1 lSL, ← map_mul, ← map_mul, M10]
  rcases rigid S hS3 hSz hS1 hS2 with hS' | hS' | hS'
  ·
    exfalso
    apply sbU_ne_one
    have h1' : c sbU = 1 := by rw [hcS, hS', map_one]
    have h2' : ψ sbU = 1 := by
      rw [hc] at h1'
      simpa using h1'
    exact hψ (h2'.trans (map_one ψ).symm)
  · left
    have : c = ψ := hom_ext_H_sbU (fun x => hc0 x) (fun x => hc1 x) (by rw [hcS, hS']; rfl)
    intro g
    rw [← hc, this]
  · right
    have h3 : c = ψ.comp (MulAut.conj (longInv F3 2 0)).toMonoidHom := by
      refine hom_ext_H_sbU (fun x => ?_) (fun x => ?_) ?_
      · rw [hc0 x, MonoidHom.comp_apply]
        show _ = ψ (longInv F3 2 0 * longBlock F3 2 0 x * (longInv F3 2 0)⁻¹)
        rw [longInv_comm_lb 0 x, mul_inv_cancel_right]
      · rw [hc1 x, MonoidHom.comp_apply]
        show _ = ψ (longInv F3 2 0 * longBlock F3 2 1 x * (longInv F3 2 0)⁻¹)
        rw [longInv0_comm_lb1 x, mul_inv_cancel_right]
      · rw [hcS, hS', MonoidHom.comp_apply]
        show ψ sbU⁻¹ = ψ (longInv F3 2 0 * sbU * (longInv F3 2 0)⁻¹)
        rw [longInv_inv, longInv0_sbU]
    intro g
    rw [← hc, h3]
    rfl

end CFSG.ClassicalInvolution.Q3.Q3ZB
