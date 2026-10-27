module

public import CFSG.ClassicalInvolution.WeakCT.AutExtend
public import CFSG.ClassicalInvolution.WeakCT.StandardPair

public section

namespace CFSG.GH74.L5U5

open Matrix CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

namespace IdentOdd

section Elementary

variable {K : Type} [Field K]

@[expose] def eL (c : K) : SL(2, K) := ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def eU (c : K) : SL(2, K) := ⟨!![1, c; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem coe_eL (c : K) : ((eL c : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; c, 1] := rfl

theorem coe_eU (c : K) : ((eU c : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![1, c; 0, 1] := rfl

@[expose] def flipSL (A : SL(2, K)) : SL(2, K) :=
  ⟨!![A 0 0, -A 0 1; -A 1 0, A 1 1], by
    have h := A.2
    rw [Matrix.det_fin_two] at h ⊢
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination h⟩

theorem coe_flipSL (A : SL(2, K)) :
    ((flipSL A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![A 0 0, -A 0 1; -A 1 0, A 1 1] := rfl

@[expose] def dMinus : SL(3, K) := blockSL K 3 2 1 (by omega) (torusHom K (-1))

theorem coe_dMinus : ((dMinus : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
    !![1, 0, 0; 0, -1, 0; 0, 0, -1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [dMinus, coe_blockSL_three_one, coe_torusHom]

theorem dMinus_mul_blockSL_zero (A : SL(2, K)) :
    dMinus * blockSL K 3 2 0 (by omega) A = blockSL K 3 2 0 (by omega) (flipSL A) * dMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, coe_dMinus,
      coe_blockSL_three_zero, coe_flipSL]

theorem blockSL_one_eL_comm_blockSL_zero_eU :
    blockSL K 3 2 1 (by omega) (eL 1) * blockSL K 3 2 0 (by omega) (eU 1) =
      blockSL K 3 2 0 (by omega) (eU 1) * blockSL K 3 2 1 (by omega) (eL 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
      coe_blockSL_three_zero, coe_blockSL_three_one, coe_eL, coe_eU]

theorem blockSL_one_eU_comm_blockSL_zero_eL :
    blockSL K 3 2 1 (by omega) (eU 1) * blockSL K 3 2 0 (by omega) (eL 1) =
      blockSL K 3 2 0 (by omega) (eL 1) * blockSL K 3 2 1 (by omega) (eU 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
      coe_blockSL_three_zero, coe_blockSL_three_one, coe_eL, coe_eU]

theorem entries_of_comm_eU (M : SL(2, K))
    (h : blockSL K 3 2 1 (by omega) M * blockSL K 3 2 0 (by omega) (eU 1) *
      (blockSL K 3 2 1 (by omega) M)⁻¹ * (blockSL K 3 2 0 (by omega) (eU 1))⁻¹ ∈
        Subgroup.center SL(3, K)) : M 0 0 = 1 ∧ M 0 1 = 0 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  have e : (blockSL K 3 2 1 (by omega) M * blockSL K 3 2 0 (by omega) (eU 1) *
      (blockSL K 3 2 1 (by omega) M)⁻¹ * (blockSL K 3 2 0 (by omega) (eU 1))⁻¹) *
      (blockSL K 3 2 0 (by omega) (eU 1) * blockSL K 3 2 1 (by omega) M) =
      blockSL K 3 2 1 (by omega) M * blockSL K 3 2 0 (by omega) (eU 1) := by group
  have e' := congrArg (fun g : SL(3, K) => (g : Matrix (Fin 3) (Fin 3) K)) e
  simp only [Matrix.SpecialLinearGroup.coe_mul, ← hr] at e'
  have h00 := congrFun (congrFun e' 0) 0
  have h01 := congrFun (congrFun e' 0) 1
  have h02 := congrFun (congrFun e' 0) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, coe_blockSL_three_zero, coe_blockSL_three_one,
    coe_eU, Matrix.scalar_apply, Matrix.diagonal_apply] at h00 h01 h02
  subst h00
  refine ⟨by simpa using h01, ?_⟩
  rcases h02 with h | h
  · exact absurd h one_ne_zero
  · exact h

theorem entries_of_comm_eL (M : SL(2, K))
    (h : blockSL K 3 2 1 (by omega) M * blockSL K 3 2 0 (by omega) (eL 1) *
      (blockSL K 3 2 1 (by omega) M)⁻¹ * (blockSL K 3 2 0 (by omega) (eL 1))⁻¹ ∈
        Subgroup.center SL(3, K)) : M 0 0 = 1 ∧ M 1 0 = 0 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  have e : (blockSL K 3 2 1 (by omega) M * blockSL K 3 2 0 (by omega) (eL 1) *
      (blockSL K 3 2 1 (by omega) M)⁻¹ * (blockSL K 3 2 0 (by omega) (eL 1))⁻¹) *
      (blockSL K 3 2 0 (by omega) (eL 1) * blockSL K 3 2 1 (by omega) M) =
      blockSL K 3 2 1 (by omega) M * blockSL K 3 2 0 (by omega) (eL 1) := by group
  have e' := congrArg (fun g : SL(3, K) => (g : Matrix (Fin 3) (Fin 3) K)) e
  simp only [Matrix.SpecialLinearGroup.coe_mul, ← hr] at e'
  have h00 := congrFun (congrFun e' 0) 0
  have h10 := congrFun (congrFun e' 1) 0
  have h20 := congrFun (congrFun e' 2) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three, coe_blockSL_three_zero, coe_blockSL_three_one,
    coe_eL, Matrix.scalar_apply, Matrix.diagonal_apply] at h00 h10 h20
  subst h00
  exact ⟨h10.symm, h20.symm⟩

theorem g01_mul_g11_of_entries (h2 : (2 : K) ≠ 0) (G : Matrix (Fin 2) (Fin 2) K)
    (ψ : K ≃+* K) (Q Q' M : SL(2, K))
    (hQ : (Q : Matrix (Fin 2) (Fin 2) K) * G =
      G * ((eL (1 : K) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).map ψ)
    (hQ' : (Q' : Matrix (Fin 2) (Fin 2) K) * G = G * (M : Matrix (Fin 2) (Fin 2) K).map ψ)
    (hflip : Q' = flipSL Q) (hM0 : M 0 0 = 1) (hM1 : M 0 1 = 0) : G 0 1 * G 1 1 = 0 := by
  have hM11 : M 1 1 = 1 := by
    have h := M.2
    rw [Matrix.det_fin_two, hM0, hM1] at h
    simpa using h
  subst hflip
  have a01 := congrFun (congrFun hQ 0) 1
  have a00 := congrFun (congrFun hQ 0) 0
  have b01 := congrFun (congrFun hQ' 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, coe_eL, coe_flipSL, hM1, hM11] at a01 a00 b01
  by_contra hne
  have hg01 : G 0 1 ≠ 0 := left_ne_zero_of_mul hne
  have hg11 : G 1 1 ≠ 0 := right_ne_zero_of_mul hne
  have h1 : Q 0 1 * G 1 1 = 0 := by
    have : (2 : K) * (Q 0 1 * G 1 1) = 0 := by linear_combination a01 - b01
    exact (mul_eq_zero.mp this).resolve_left h2
  have hq01 : Q 0 1 = 0 := (mul_eq_zero.mp h1).resolve_right hg11
  have hq00 : Q 0 0 = 1 := by
    have : (Q 0 0 - 1) * G 0 1 = 0 := by linear_combination a01 - G 1 1 * hq01
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hg01)
  apply hg01
  linear_combination (-1 : K) * a00 + G 0 0 * hq00 + G 1 0 * hq01

theorem g00_mul_g10_of_entries (h2 : (2 : K) ≠ 0) (G : Matrix (Fin 2) (Fin 2) K)
    (ψ : K ≃+* K) (Q Q' M : SL(2, K))
    (hQ : (Q : Matrix (Fin 2) (Fin 2) K) * G =
      G * ((eU (1 : K) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).map ψ)
    (hQ' : (Q' : Matrix (Fin 2) (Fin 2) K) * G = G * (M : Matrix (Fin 2) (Fin 2) K).map ψ)
    (hflip : Q' = flipSL Q) (hM0 : M 0 0 = 1) (hM1 : M 1 0 = 0) : G 0 0 * G 1 0 = 0 := by
  have hM11 : M 1 1 = 1 := by
    have h := M.2
    rw [Matrix.det_fin_two, hM0, hM1] at h
    simpa using h
  subst hflip
  have a00 := congrFun (congrFun hQ 0) 0
  have a10 := congrFun (congrFun hQ 1) 0
  have a11 := congrFun (congrFun hQ 1) 1
  have b00 := congrFun (congrFun hQ' 0) 0
  have b10 := congrFun (congrFun hQ' 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, coe_eU, coe_flipSL, hM0, hM1] at a00 a10 a11 b00 b10
  by_contra hne
  have hg00 : G 0 0 ≠ 0 := left_ne_zero_of_mul hne
  have hg10 : G 1 0 ≠ 0 := right_ne_zero_of_mul hne
  have h1 : Q 1 0 * G 0 0 = 0 := by
    have : (2 : K) * (Q 1 0 * G 0 0) = 0 := by linear_combination a10 - b10
    exact (mul_eq_zero.mp this).resolve_left h2
  have hq10 : Q 1 0 = 0 := (mul_eq_zero.mp h1).resolve_right hg00
  have hq11 : Q 1 1 = 1 := by
    have : (Q 1 1 - 1) * G 1 0 = 0 := by linear_combination a10 - G 0 0 * hq10
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hg10)
  apply hg10
  linear_combination (-1 : K) * a11 + G 0 1 * hq10 + G 1 1 * hq11

end Elementary

end IdentOdd

open IdentOdd

section Monomial

variable {K : Type} [Field K] {X : Type} [Group X]

theorem g01_mul_g11_eq_zero (h2 : (2 : K) ≠ 0) {θ θ₀ : SL(3, K) →* X}
    (hθ : θ.ker ≤ Subgroup.center SL(3, K))
    (hcomm : ∀ x ∈ (B12 K).map θ, ∀ y ∈ (B23 K).map θ₀, x * y = y * x)
    (α : SL(2, K) ≃* SL(2, K))
    (hα : ∀ A, θ₀ (blockSL K 3 2 0 (by omega) (α A)) = θ (blockSL K 3 2 1 (by omega) A))
    (G : Matrix (Fin 2) (Fin 2) K) (ψ : K ≃+* K)
    (hR : ∀ A : SL(2, K), ((α A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * G =
      G * (A : Matrix (Fin 2) (Fin 2) K).map ψ) : G 0 1 * G 1 1 = 0 := by
  set x := blockSL K 3 2 0 (by omega) (eU (1 : K)) with hx
  set u : SL(2, K) := eL 1 with hu
  set M' : SL(2, K) := α.symm (flipSL (α u)) with hM'
  have hst : Commute (θ (blockSL K 3 2 1 (by omega) u)) (θ x) := by
    show _ * _ = _ * _
    rw [← map_mul, ← map_mul, hx, hu, blockSL_one_eL_comm_blockSL_zero_eU]
  have hv : Commute (θ₀ dMinus) (θ x) :=
    (hcomm _ ⟨x, ⟨eU 1, rfl⟩, rfl⟩ _ ⟨dMinus, ⟨torusHom K (-1), rfl⟩, rfl⟩).symm
  have key : θ (blockSL K 3 2 1 (by omega) M') =
      θ₀ dMinus * θ (blockSL K 3 2 1 (by omega) u) * (θ₀ dMinus)⁻¹ := by
    rw [← hα M', hM', MulEquiv.apply_symm_apply, ← hα u]
    have h1 : blockSL K 3 2 0 (by omega) (flipSL (α u)) =
        dMinus * blockSL K 3 2 0 (by omega) (α u) * dMinus⁻¹ := by
      calc blockSL K 3 2 0 (by omega) (flipSL (α u))
          = blockSL K 3 2 0 (by omega) (flipSL (α u)) * dMinus * dMinus⁻¹ := by group
        _ = _ := by rw [← dMinus_mul_blockSL_zero]
    rw [h1, map_mul, map_mul, map_inv]
  have hcommM : Commute (θ (blockSL K 3 2 1 (by omega) M')) (θ x) := by
    rw [key]
    exact (hv.mul_left hst).mul_left hv.inv_left
  have hmem : blockSL K 3 2 1 (by omega) M' * x * (blockSL K 3 2 1 (by omega) M')⁻¹ * x⁻¹ ∈
      Subgroup.center SL(3, K) := by
    apply hθ
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hcommM.eq]
    group
  obtain ⟨hM0, hM1⟩ := entries_of_comm_eU M' hmem
  exact g01_mul_g11_of_entries h2 G ψ (α u) (α M') M' (hR u) (hR M')
    (by rw [hM', MulEquiv.apply_symm_apply]) hM0 hM1

theorem g00_mul_g10_eq_zero (h2 : (2 : K) ≠ 0) {θ θ₀ : SL(3, K) →* X}
    (hθ : θ.ker ≤ Subgroup.center SL(3, K))
    (hcomm : ∀ x ∈ (B12 K).map θ, ∀ y ∈ (B23 K).map θ₀, x * y = y * x)
    (α : SL(2, K) ≃* SL(2, K))
    (hα : ∀ A, θ₀ (blockSL K 3 2 0 (by omega) (α A)) = θ (blockSL K 3 2 1 (by omega) A))
    (G : Matrix (Fin 2) (Fin 2) K) (ψ : K ≃+* K)
    (hR : ∀ A : SL(2, K), ((α A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * G =
      G * (A : Matrix (Fin 2) (Fin 2) K).map ψ) : G 0 0 * G 1 0 = 0 := by
  set x := blockSL K 3 2 0 (by omega) (eL (1 : K)) with hx
  set u : SL(2, K) := eU 1 with hu
  set M' : SL(2, K) := α.symm (flipSL (α u)) with hM'
  have hst : Commute (θ (blockSL K 3 2 1 (by omega) u)) (θ x) := by
    show _ * _ = _ * _
    rw [← map_mul, ← map_mul, hx, hu, blockSL_one_eU_comm_blockSL_zero_eL]
  have hv : Commute (θ₀ dMinus) (θ x) :=
    (hcomm _ ⟨x, ⟨eL 1, rfl⟩, rfl⟩ _ ⟨dMinus, ⟨torusHom K (-1), rfl⟩, rfl⟩).symm
  have key : θ (blockSL K 3 2 1 (by omega) M') =
      θ₀ dMinus * θ (blockSL K 3 2 1 (by omega) u) * (θ₀ dMinus)⁻¹ := by
    rw [← hα M', hM', MulEquiv.apply_symm_apply, ← hα u]
    have h1 : blockSL K 3 2 0 (by omega) (flipSL (α u)) =
        dMinus * blockSL K 3 2 0 (by omega) (α u) * dMinus⁻¹ := by
      calc blockSL K 3 2 0 (by omega) (flipSL (α u))
          = blockSL K 3 2 0 (by omega) (flipSL (α u)) * dMinus * dMinus⁻¹ := by group
        _ = _ := by rw [← dMinus_mul_blockSL_zero]
    rw [h1, map_mul, map_mul, map_inv]
  have hcommM : Commute (θ (blockSL K 3 2 1 (by omega) M')) (θ x) := by
    rw [key]
    exact (hv.mul_left hst).mul_left hv.inv_left
  have hmem : blockSL K 3 2 1 (by omega) M' * x * (blockSL K 3 2 1 (by omega) M')⁻¹ * x⁻¹ ∈
      Subgroup.center SL(3, K) := by
    apply hθ
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hcommM.eq]
    group
  obtain ⟨hM0, hM1⟩ := entries_of_comm_eL M' hmem
  exact g00_mul_g10_of_entries h2 G ψ (α u) (α M') M' (hR u) (hR M')
    (by rw [hM', MulEquiv.apply_symm_apply]) hM0 hM1

theorem monomial_of_commute [Finite K] (h2 : (2 : K) ≠ 0) {θ θ₀ : SL(3, K) →* X}
    (hθ : θ.ker ≤ Subgroup.center SL(3, K))
    (hcomm : ∀ x ∈ (B12 K).map θ, ∀ y ∈ (B23 K).map θ₀, x * y = y * x)
    (α : SL(2, K) ≃* SL(2, K))
    (hα : ∀ A, θ₀ (blockSL K 3 2 0 (by omega) (α A)) = θ (blockSL K 3 2 1 (by omega) A))
    (G : GL (Fin 2) K) (ψ : K ≃+* K)
    (hG : ∀ A : SL(2, K), Matrix.SpecialLinearGroup.toGL (α A) =
      G * Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (ψ : K →+* K) A) * G⁻¹) :
    ((G : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧ (G : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) ∨
      ((G : Matrix (Fin 2) (Fin 2) K) 0 0 = 0 ∧ (G : Matrix (Fin 2) (Fin 2) K) 1 1 = 0) := by
  have hR : ∀ A : SL(2, K), ((α A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
      (G : Matrix (Fin 2) (Fin 2) K) =
      (G : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K).map ψ := by
    intro A
    have h1 : Matrix.SpecialLinearGroup.toGL (α A) * G =
        G * Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (ψ : K →+* K) A) :=
      eq_mul_inv_iff_mul_eq.mp (hG A)
    have h2' := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) h1
    simp only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at h2'
    exact h2'
  have e1 := g01_mul_g11_eq_zero h2 hθ hcomm α hα (G : Matrix (Fin 2) (Fin 2) K) ψ hR
  have e2 := g00_mul_g10_eq_zero h2 hθ hcomm α hα (G : Matrix (Fin 2) (Fin 2) K) ψ hR
  have hdet : (G : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := (Matrix.isUnits_det_units G).ne_zero
  rw [Matrix.det_fin_two] at hdet
  by_cases h00 : (G : Matrix (Fin 2) (Fin 2) K) 0 0 = 0
  · right
    refine ⟨h00, ?_⟩
    have hg01 : (G : Matrix (Fin 2) (Fin 2) K) 0 1 ≠ 0 := fun h => hdet (by rw [h00, h]; ring)
    exact (mul_eq_zero.mp e1).resolve_left hg01
  · left
    have hg10 : (G : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := (mul_eq_zero.mp e2).resolve_left h00
    refine ⟨?_, hg10⟩
    have hg11 : (G : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := fun h => hdet (by rw [h, hg10]; ring)
    exact (mul_eq_zero.mp e1).resolve_right hg11

end Monomial

section Extend

variable {K : Type} [Field K]

theorem exists_extend_of_monomial [Finite K] (α : SL(2, K) ≃* SL(2, K)) (G : GL (Fin 2) K)
    (ψ : K ≃+* K)
    (hG : ∀ A : SL(2, K), Matrix.SpecialLinearGroup.toGL (α A) =
      G * Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (ψ : K →+* K) A) * G⁻¹)
    (hmono : ((G : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧ (G : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) ∨
      ((G : Matrix (Fin 2) (Fin 2) K) 0 0 = 0 ∧ (G : Matrix (Fin 2) (Fin 2) K) 1 1 = 0)) :
    ∃ β : SL(3, K) ≃* SL(3, K),
      (∀ A, β (blockSL K 3 2 0 (by omega) A) = blockSL K 3 2 0 (by omega) (α A)) ∧
        (B23 K).map β.toMonoidHom = B23 K := by
  have hcoe : ∀ A : SL(2, K), ((α A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      (G : Matrix (Fin 2) (Fin 2) K) *
        ((Matrix.SpecialLinearGroup.map (ψ : K →+* K) A : SL(2, K)) :
          Matrix (Fin 2) (Fin 2) K) * ((G⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    intro A
    have h2 := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) (hG A)
    simpa only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using h2
  rcases hmono with ⟨h01, h10⟩ | ⟨h00, h11⟩
  · obtain ⟨a, b, hGa, hGi⟩ := exists_diagonal_of_offDiag_zero G h01 h10
    have hα' : ∀ A, α A = diagConj2 a b (fieldAutSL ψ 2 A) := fun A =>
      Subtype.ext (by rw [hcoe A, hGa, hGi]; rfl)
    have hβ0 : ∀ A, (fieldAutSL ψ 3).trans (diagConj3 a b) (blockSL K 3 2 0 (by omega) A) =
        blockSL K 3 2 0 (by omega) (α A) := fun A => by
      show diagConj3 a b (fieldAutSL ψ 3 (blockSL K 3 2 0 _ A)) = _
      rw [fieldAutSL_blockSL, diagConj3_blockSL_zero, hα']
    refine ⟨(fieldAutSL ψ 3).trans (diagConj3 a b), hβ0, map_B23_eq _ fun C => ?_⟩
    show diagConj3 a b (fieldAutSL ψ 3 (blockSL K 3 2 1 _ C)) ∈ B23 K
    rw [fieldAutSL_blockSL, diagConj3_blockSL_one]
    exact ⟨_, rfl⟩
  · obtain ⟨a, b, hab⟩ := exists_diagonal_of_diag_zero G h00 h11
    have hα' : ∀ A, α A = diagConj2 a b (invTransposeSL 2 (fieldAutSL ψ 2 A)) := fun A =>
      Subtype.ext ((hcoe A).trans (hab _))
    have hβ0 : ∀ A, ((fieldAutSL ψ 3).trans (invTransposeSL 3)).trans (diagConj3 a b)
        (blockSL K 3 2 0 (by omega) A) = blockSL K 3 2 0 (by omega) (α A) := fun A => by
      show diagConj3 a b (invTransposeSL 3 (fieldAutSL ψ 3 (blockSL K 3 2 0 _ A))) = _
      rw [fieldAutSL_blockSL, invTransposeSL_blockSL, diagConj3_blockSL_zero, hα']
    refine ⟨((fieldAutSL ψ 3).trans (invTransposeSL 3)).trans (diagConj3 a b), hβ0,
      map_B23_eq _ fun C => ?_⟩
    show diagConj3 a b (invTransposeSL 3 (fieldAutSL ψ 3 (blockSL K 3 2 1 _ C))) ∈ B23 K
    rw [fieldAutSL_blockSL, invTransposeSL_blockSL, diagConj3_blockSL_one]
    exact ⟨_, rfl⟩

end Extend

section Adjust

variable {K : Type} [Field K] [Finite K] {X : Type} [Group X]

theorem exists_adjust_odd (h2 : (2 : K) ≠ 0) {θ θ₀ : SL(3, K) →* X} {V₀ V₁ V₂ : Subgroup X}
    (hθ : θ.ker ≤ Subgroup.center SL(3, K)) (hθ₀ : θ₀.ker ≤ Subgroup.center SL(3, K))
    (h0 : (B12 K).map θ = V₀) (h1 : (B23 K).map θ = V₁) (h1' : (B12 K).map θ₀ = V₁)
    (h2' : (B23 K).map θ₀ = V₂) (hcomm : ∀ x ∈ V₀, ∀ y ∈ V₂, x * y = y * x) :
    ∃ θ' : SL(3, K) →* X, θ'.ker ≤ Subgroup.center SL(3, K) ∧ (B12 K).map θ' = V₁ ∧
      (B23 K).map θ' = V₂ ∧
      θ'.comp (blockSL K 3 2 0 (by omega)) = θ.comp (blockSL K 3 2 1 (by omega)) := by
  have hm₁ : Function.Injective (θ.comp (blockSL K 3 2 1 (by omega))) :=
    comp_blockSL_injective hθ _ (by omega)
  have hm₂ : Function.Injective (θ₀.comp (blockSL K 3 2 0 (by omega))) :=
    comp_blockSL_injective hθ₀ _ (by omega)
  have hr₁ : (θ.comp (blockSL K 3 2 1 (by omega))).range = V₁ := by
    rw [MonoidHom.range_comp, ← h1]
    rfl
  have hr₂ : (θ₀.comp (blockSL K 3 2 0 (by omega))).range = V₁ := by
    rw [MonoidHom.range_comp, ← h1']
    rfl
  have hrr : (θ.comp (blockSL K 3 2 1 (by omega))).range =
      (θ₀.comp (blockSL K 3 2 0 (by omega))).range := hr₁.trans hr₂.symm
  let α : SL(2, K) ≃* SL(2, K) :=
    (MonoidHom.ofInjective hm₁).trans
      ((MulEquiv.subgroupCongr hrr).trans (MonoidHom.ofInjective hm₂).symm)
  have hα : ∀ A, θ₀ (blockSL K 3 2 0 (by omega) (α A)) = θ (blockSL K 3 2 1 (by omega) A) := by
    intro A
    have h := congrArg Subtype.val ((MonoidHom.ofInjective hm₂).apply_symm_apply
      (MulEquiv.subgroupCongr hrr (MonoidHom.ofInjective hm₁ A)))
    exact h
  obtain ⟨G, ψ, hG⟩ := CFSG.ClassicalInvolution.Phan.exists_toGL_eq_conj_map α
  have hmono := monomial_of_commute h2 hθ
    (fun x hx y hy => hcomm x (h0 ▸ hx) y (h2' ▸ hy)) α hα G ψ hG
  obtain ⟨β, hβ0, hβ1⟩ := exists_extend_of_monomial α G ψ hG hmono
  have hB12 : (B12 K).map β.toMonoidHom = B12 K := by
    ext x
    constructor
    · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
      exact ⟨α A, (hβ0 A).symm⟩
    · rintro ⟨A, rfl⟩
      refine ⟨blockSL K 3 2 0 (by omega) (α.symm A), ⟨_, rfl⟩, ?_⟩
      show β (blockSL K 3 2 0 (by omega) (α.symm A)) = _
      rw [hβ0, MulEquiv.apply_symm_apply]
  refine ⟨θ₀.comp β.toMonoidHom, ker_comp_mulEquiv_le_center hθ₀ β, ?_, ?_, ?_⟩
  · rw [map_comp_mulEquiv, hB12, h1']
  · rw [map_comp_mulEquiv, hβ1, h2']
  · refine MonoidHom.ext fun A => ?_
    show θ₀ (β (blockSL K 3 2 0 (by omega) A)) = θ (blockSL K 3 2 1 (by omega) A)
    rw [hβ0, hα]

end Adjust

end CFSG.GH74.L5U5
