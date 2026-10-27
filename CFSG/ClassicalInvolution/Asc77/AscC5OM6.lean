module

public import CFSG.ClassicalInvolution.Asc77.AscC5OM4

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O.M

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped Matrix

variable {F : Type} [Field F]

@[expose] def bX (F : Type) [Field F] : Matrix (Fin 2) (Fin 2) F := !![1, 1; -1, 1]

@[expose] def xMatM (F : Type) [Field F] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks (bX F) 0 0 ((2 : F)⁻¹ • bX F)

theorem xMatM_symplectic (h2 : (2 : F) ≠ 0) : (xMatM F)ᵀ * gram F 2 * xMatM F = gram F 2 := by
  rw [xMatM, gram, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  have e1 : (bX F)ᵀ * ((2 : F)⁻¹ • bX F) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [bX, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> norm_num
  have e2 : ((2 : F)⁻¹ • bX F)ᵀ * bX F = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [bX, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> norm_num
  simp only [Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
    Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul]
  rw [e1, e2, neg_zero]

@[expose] noncomputable def xMat (h2 : (2 : F) ≠ 0) : StatedSp 2 F :=
  ofSymplecticMat (xMatM F) (xMatM_symplectic h2)

theorem mat_longInv_zero :
    mat 2 F (longInv F 2 0) =
      Matrix.fromBlocks !![-1, 0; 0, 1] 0 0 !![-1, 0; 0, 1] := by
  rw [mat_longInv]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [mem_coords]

theorem mat_longInv_one' :
    mat 2 F (longInv F 2 1) =
      Matrix.fromBlocks !![1, 0; 0, -1] 0 0 !![1, 0; 0, -1] := by
  rw [mat_longInv]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [mem_coords]

theorem xMat_mul_longInv (h2 : (2 : F) ≠ 0) :
    xMat h2 * longInv F 2 0 = sw F * xMat h2 := by
  apply mat_injective
  rw [map_mul, map_mul, mat_sw, mat_longInv_zero]
  change xMatM F * _ = swMat F * xMatM F
  rw [xMatM, swMat, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.smul_mul,
    Matrix.mul_smul]
  have e : bX F * !![-1, 0; 0, 1] = perm2 F * bX F := by
    simp [bX, perm2]
  rw [e, smul_zero]

theorem xMat_mul_sw (h2 : (2 : F) ≠ 0) :
    xMat h2 * sw F = longInv F 2 1 * xMat h2 := by
  apply mat_injective
  rw [map_mul, map_mul, mat_sw, mat_longInv_one']
  change xMatM F * swMat F = _ * xMatM F
  rw [xMatM, swMat, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.smul_mul,
    Matrix.mul_smul]
  have e : bX F * perm2 F = !![1, 0; 0, -1] * bX F := by
    simp [bX, perm2]
  rw [e, smul_zero]

theorem xMat_conj_longInv (h2 : (2 : F) ≠ 0) :
    xMat h2 * longInv F 2 0 * (xMat h2)⁻¹ = sw F := by
  rw [xMat_mul_longInv, mul_inv_cancel_right]

theorem xMat_conj_sw (h2 : (2 : F) ≠ 0) :
    xMat h2 * sw F * (xMat h2)⁻¹ = longInv F 2 1 := by
  rw [xMat_mul_sw, mul_inv_cancel_right]

theorem map_conj_L_eq (h2 : (2 : F) ≠ 0) (k l : Fin 2) {h : StatedSp 2 F}
    (hc : h * longInv F 2 k * h⁻¹ = longInv F 2 l) :
    (longRootSp2 F 2 k).map (MulAut.conj h).toMonoidHom = longRootSp2 F 2 l := by
  have hL := (isLongRootSp2_standard (K := F) (n := 2) k).conj h
  rw [hc] at hL
  rw [hL.eq_longRootGroup h2, (isLongRootSp2_standard (K := F) (n := 2) l).eq_longRootGroup h2]

theorem longInv_one_mul_zero :
    longInv F 2 1 * longInv F 2 0 = negOne F := by
  rw [negOne, longInv_comm_L 1 0 (longInv_mem 0)]

namespace Frame

variable {Y : Type} [Group Y] {Φ : Set (Subgroup Y)} {A A' : Subgroup Y} {z' : Y}
  (fr : Frame F Y Φ A A' z')
include fr

theorem zSwap (h2 : (2 : F) ≠ 0) :
    ∃ s : Y, s * s = 1 ∧ conjSub s A = A' ∧ ∃ x : Y, x * z' * x⁻¹ = s := by
  refine ⟨fr.ψ (sw F), ?_, ?_, fr.ψ (xMat h2), ?_⟩
  · rw [← map_mul, sw_mul_self, map_one]
  · calc conjSub (fr.ψ (sw F)) A = conjSub (fr.ψ (sw F)) ((longRootSp2 F 2 0).map fr.ψ) :=
          congrArg _ fr.hA
      _ = ((longRootSp2 F 2 0).map (MulAut.conj (sw F)).toMonoidHom).map fr.ψ :=
          fr.conjSub_map_ψ _ _
      _ = (longRootSp2 F 2 1).map fr.ψ := by rw [map_sw_L h2 0]; rfl
      _ = A' := fr.hA'.symm
  · have h := congrArg fr.ψ (xMat_conj_longInv h2)
    rw [map_mul, map_mul, map_inv, ← fr.hz] at h
    exact h

theorem swap_lift (h2 : (2 : F) ≠ 0) (hne : A ≠ A') (hzA : IsUniqueInvolution A z')
    (hzA' : IsUniqueInvolution A' z') {t : StatedSp 2 F} (ht : conjSub (fr.ψ t) A = A') :
    t * longInv F 2 0 * t⁻¹ = longInv F 2 1 := by
  have hz1 : fr.ψ t * z' * (fr.ψ t)⁻¹ = z' := by
    have := hzA.conj (fr.ψ t)
    rw [ht] at this
    exact (hzA'.eq this).symm
  rcases fr.conj_longInv_cases hz1 with hc | hc
  · exfalso
    apply hne
    calc A = (longRootSp2 F 2 0).map fr.ψ := fr.hA
      _ = ((longRootSp2 F 2 0).map (MulAut.conj t).toMonoidHom).map fr.ψ := by
          rw [map_conj_L_eq h2 0 0 hc]
      _ = conjSub (fr.ψ t) ((longRootSp2 F 2 0).map fr.ψ) := (fr.conjSub_map_ψ _ _).symm
      _ = conjSub (fr.ψ t) A := (congrArg _ fr.hA).symm
      _ = A' := ht
  · exact hc

theorem uSwapNotZ [Finite F] (h2 : (2 : F) ≠ 0) (hne : A ≠ A') (hzA : IsUniqueInvolution A z')
    (hzA' : IsUniqueInvolution A' z') {s : Y} (hs : conjSub s A = A')
    (hsz : ∃ x : Y, x * z' * x⁻¹ = s) (β : Y ≃* Y) : β z' ≠ s * z' := by
  obtain ⟨x, rfl⟩ := hsz
  obtain ⟨X₁, rfl⟩ := fr.surj x
  have hψt : fr.ψ (X₁ * longInv F 2 0 * X₁⁻¹) = fr.ψ X₁ * z' * (fr.ψ X₁)⁻¹ := by
    rw [map_mul, map_mul, map_inv, ← fr.hz]
  rw [← hψt] at hs ⊢
  have ht2 : X₁ * longInv F 2 0 * X₁⁻¹ * (X₁ * longInv F 2 0 * X₁⁻¹) = 1 := by
    calc X₁ * longInv F 2 0 * X₁⁻¹ * (X₁ * longInv F 2 0 * X₁⁻¹) =
        X₁ * (longInv F 2 0 * longInv F 2 0) * X₁⁻¹ := by group
      _ = 1 := by rw [longInv_mul_self]; group
  generalize X₁ * longInv F 2 0 * X₁⁻¹ = t at hs ht2 ⊢
  have hc := fr.swap_lift h2 hne hzA hzA' hs
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hti : t * longInv F 2 0 * (t * longInv F 2 0) = negOne F := by
    calc t * longInv F 2 0 * (t * longInv F 2 0) = (t * longInv F 2 0 * t⁻¹) * longInv F 2 0 := by
          rw [htinv]; group
      _ = negOne F := by rw [hc, longInv_one_mul_zero]
  obtain ⟨M, σ, hβ⟩ := fr.exists_lift_aut h2 β
  intro heq
  have hj : fr.ψ (conjSp 2 F M (fieldSp 2 F σ (longInv F 2 0))) =
      fr.ψ (t * longInv F 2 0) := by
    rw [← hβ, ← fr.hz, heq, map_mul, ← fr.hz]
  have hj2 : conjSp 2 F M (fieldSp 2 F σ (longInv F 2 0)) *
      conjSp 2 F M (fieldSp 2 F σ (longInv F 2 0)) = 1 := by
    rw [← map_mul, ← map_mul, longInv_mul_self, map_one, map_one]
  rcases fr.lift_eq_iff.mp hj with h | h
  · rw [h, hti] at hj2
    exact negOne_ne_one h2 hj2
  · rw [h] at hj2
    have e : t * longInv F 2 0 * negOne F * (t * longInv F 2 0 * negOne F) =
        t * longInv F 2 0 * (t * longInv F 2 0) * (negOne F * negOne F) := by
      calc t * longInv F 2 0 * negOne F * (t * longInv F 2 0 * negOne F) =
          t * longInv F 2 0 * (negOne F * (t * longInv F 2 0)) * negOne F := by group
        _ = t * longInv F 2 0 * (t * longInv F 2 0 * negOne F) * negOne F := by
          rw [negOne_comm]
        _ = t * longInv F 2 0 * (t * longInv F 2 0) * (negOne F * negOne F) := by group
    rw [e, hti, negOne_mul_self, mul_one] at hj2
    exact negOne_ne_one h2 hj2

end Frame

end CFSG.ClassicalInvolution.Asc77.C5O.M
