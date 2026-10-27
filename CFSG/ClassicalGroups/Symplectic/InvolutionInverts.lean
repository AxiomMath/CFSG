module

public import CFSG.Blueprint.Catalog
import CFSG.ClassicalGroups.SpecialLinear.InvolutionInverts
import CFSG.Quasithin.EmptyFaithful.R3cBase

public section

open Matrix

namespace CFSG.ClassicalGroups.Symplectic

namespace InvolutionInverts

section Embed

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {K : Type*}
  [Field K]

private def embedMat (A : Matrix ι κ K) (B : Matrix κ ι K) (R : Matrix κ κ K) : Matrix ι ι K :=
  1 + A * (R - 1) * B

private theorem embedMat_one (A : Matrix ι κ K) (B : Matrix κ ι K) : embedMat A B 1 = 1 := by
  simp [embedMat]

private theorem mul_cancel_left_of_mul_eq_one {A : Matrix ι κ K} {B : Matrix κ ι K}
    (hBA : B * A = 1) {n : Type*} (X : Matrix κ n K) : B * (A * X) = X := by
  rw [← Matrix.mul_assoc, hBA, Matrix.one_mul]

private theorem embedMat_mul {A : Matrix ι κ K} {B : Matrix κ ι K} (hBA : B * A = 1)
    (R S : Matrix κ κ K) : embedMat A B (R * S) = embedMat A B R * embedMat A B S := by
  have h := fun X : Matrix κ ι K => mul_cancel_left_of_mul_eq_one hBA X
  unfold embedMat
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_assoc, h]
  abel

private theorem embedMat_injective {A : Matrix ι κ K} {B : Matrix κ ι K} (hBA : B * A = 1)
    {R S : Matrix κ κ K} (h : embedMat A B R = embedMat A B S) : R = S := by
  have h1 := fun X : Matrix κ κ K => mul_cancel_left_of_mul_eq_one hBA X
  have key : ∀ T : Matrix κ κ K, B * embedMat A B T * A = T := by
    intro T
    unfold embedMat
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_assoc, h1, hBA]
    abel
  rw [← key R, ← key S, h]

private theorem transpose_eq_of_mul_eq_one {G H : Matrix κ κ K} (hG : Gᵀ = G) (hHG : H * G = 1) :
    Hᵀ = H := by
  have h : G * Hᵀ = 1 := by
    have := congrArg Matrix.transpose hHG
    rwa [Matrix.transpose_mul, hG, Matrix.transpose_one] at this
  calc Hᵀ = (H * G) * Hᵀ := by rw [hHG, Matrix.one_mul]
    _ = H := by rw [Matrix.mul_assoc, h, Matrix.mul_one]

private theorem sandwich_eq_zero {G H R : Matrix κ κ K} (hGH : G * H = 1) (hHG : H * G = 1)
    (hR : Rᵀ * G * R = G) :
    (R - 1) * H + H * (Rᵀ - 1) + H * (Rᵀ - 1) * G * (R - 1) * H = 0 := by
  calc (R - 1) * H + H * (Rᵀ - 1) + H * (Rᵀ - 1) * G * (R - 1) * H
      = (R - 1) * H + H * (Rᵀ - 1) +
        (H * (Rᵀ * G * R) * H - H * Rᵀ * (G * H) - (H * G) * R * H + H * G * H) := by
        noncomm_ring
    _ = (R - 1) * H + H * (Rᵀ - 1) + (1 * H - H * Rᵀ * 1 - 1 * R * H + 1 * H) := by
        rw [hR, hGH, hHG]
    _ = 0 := by noncomm_ring

private theorem embedMat_isometry {J : Matrix ι ι K} (hJ : Jᵀ = J) {A : Matrix ι κ K}
    {G H : Matrix κ κ K} (hG : Aᵀ * J * A = G) (hGH : G * H = 1) (hHG : H * G = 1)
    {R : Matrix κ κ K} (hR : Rᵀ * G * R = G) :
    (embedMat A (H * Aᵀ * J) R)ᵀ * J * embedMat A (H * Aᵀ * J) R = J := by
  have hGt : Gᵀ = G := by
    rw [← hG, Matrix.transpose_mul, Matrix.transpose_mul, hJ, Matrix.transpose_transpose,
      Matrix.mul_assoc]
  have hHt := transpose_eq_of_mul_eq_one hGt hHG
  have hX := sandwich_eq_zero hGH hHG hR
  have hE : (embedMat A (H * Aᵀ * J) R)ᵀ * J * embedMat A (H * Aᵀ * J) R =
      J + (J * A) * ((R - 1) * H + H * (Rᵀ - 1) +
        H * (Rᵀ - 1) * (Aᵀ * J * A) * (R - 1) * H) * (Aᵀ * J) := by
    unfold embedMat
    simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_sub,
      Matrix.transpose_one, Matrix.transpose_transpose, hJ, hHt, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    abel
  rw [hE, hG, hX, Matrix.mul_zero, Matrix.zero_mul, add_zero]

private theorem embedMat_conj {A : Matrix ι κ K} {B : Matrix κ ι K} {u : Matrix ι ι K}
    {U : Matrix κ κ K} (hu2 : u * u = 1) (hU2 : U * U = 1) (hUA : u * A = A * U)
    (hBu : B * u = U * B) (R : Matrix κ κ K) :
    u * embedMat A B R * u = embedMat A B (U * R * U) := by
  have h1 : u * (A * (R - 1) * B) * u = A * (U * R * U - 1) * B := by
    calc u * (A * (R - 1) * B) * u = (u * A) * (R - 1) * (B * u) := by
          simp only [Matrix.mul_assoc]
      _ = (A * U) * (R - 1) * (U * B) := by rw [hUA, hBu]
      _ = A * (U * R * U - U * U) * B := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
            Matrix.mul_assoc]
      _ = A * (U * R * U - 1) * B := by rw [hU2]
  unfold embedMat
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, hu2]
  rw [h1]

private theorem proj_mul_involution {J : Matrix ι ι K} (hJ : Jᵀ = J) {u : Matrix ι ι K}
    (hu : uᵀ * J * u = J) (hu2 : u * u = 1) {A : Matrix ι κ K} {G H U : Matrix κ κ K}
    (hG : Aᵀ * J * A = G) (hGH : G * H = 1) (hHG : H * G = 1) (hU2 : U * U = 1)
    (hUA : u * A = A * U) : (H * Aᵀ * J) * u = U * (H * Aᵀ * J) := by
  have hJu : J * u = uᵀ * J := by
    calc J * u = (uᵀ * J * u) * u := by rw [hu]
      _ = uᵀ * J := by rw [Matrix.mul_assoc, hu2, Matrix.mul_one]
  have hUG : Uᵀ * G * U = G := by
    calc Uᵀ * G * U = (A * U)ᵀ * J * (A * U) := by
          rw [← hG, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = (u * A)ᵀ * J * (u * A) := by rw [hUA]
      _ = Aᵀ * (uᵀ * J * u) * A := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = G := by rw [hu, ← hG, Matrix.mul_assoc]
  have hGU : G * U = Uᵀ * G := by
    calc G * U = (Uᵀ * G * U) * U := by rw [hUG]
      _ = Uᵀ * G := by rw [Matrix.mul_assoc, hU2, Matrix.mul_one]
  have hHU : H * Uᵀ = U * H := by
    calc H * Uᵀ = H * (Uᵀ * G) * H := by
          rw [Matrix.mul_assoc H, Matrix.mul_assoc Uᵀ, hGH, Matrix.mul_one]
      _ = (H * G) * U * H := by rw [← hGU]; simp only [Matrix.mul_assoc]
      _ = U * H := by rw [hHG, Matrix.one_mul]
  calc (H * Aᵀ * J) * u = H * Aᵀ * (J * u) := by rw [Matrix.mul_assoc]
    _ = H * (Aᵀ * uᵀ) * J := by rw [hJu]; simp only [Matrix.mul_assoc]
    _ = H * (u * A)ᵀ * J := by rw [Matrix.transpose_mul]
    _ = H * (A * U)ᵀ * J := by rw [hUA]
    _ = (H * Uᵀ) * Aᵀ * J := by rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = U * (H * Aᵀ * J) := by rw [hHU]; simp only [Matrix.mul_assoc]

private noncomputable def embedHom {A : Matrix ι κ K} {B : Matrix κ ι K} (hBA : B * A = 1)
    (Φ : Matrix.SpecialLinearGroup (Fin 2) K →* Matrix κ κ K) :
    Matrix.SpecialLinearGroup (Fin 2) K →* GL ι K :=
  MonoidHom.toHomUnits
    { toFun := fun S => embedMat A B (Φ S)
      map_one' := by rw [map_one, embedMat_one]
      map_mul' := fun S S' => by rw [map_mul, embedMat_mul hBA] }

private theorem coe_embedHom {A : Matrix ι κ K} {B : Matrix κ ι K} (hBA : B * A = 1)
    (Φ : Matrix.SpecialLinearGroup (Fin 2) K →* Matrix κ κ K)
    (S : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((embedHom hBA Φ S : GL ι K) : Matrix ι ι K) = embedMat A B (Φ S) := rfl

private theorem embedHom_injective {A : Matrix ι κ K} {B : Matrix κ ι K} (hBA : B * A = 1)
    {Φ : Matrix.SpecialLinearGroup (Fin 2) K →* Matrix κ κ K} (hΦ : Function.Injective Φ) :
    Function.Injective (embedHom hBA Φ) := fun S S' h =>
  hΦ (embedMat_injective hBA (by
    have := congrArg (fun g : GL ι K => (g : Matrix ι ι K)) h
    simpa [coe_embedHom] using this))

end Embed

section SL2

variable {K : Type} [Field K] [CharP K 2]

private theorem transvection_eq_fin_two :
    transvection (1 : Fin 2) 0 (1 : K) = !![1, 0; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transvection, Matrix.single_apply]

private def tvSL : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩

private theorem tvSL_coe : ((tvSL : Matrix.SpecialLinearGroup (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K) = !![1, 0; 1, 1] := rfl

private theorem tvSL_mul_self : (tvSL : Matrix.SpecialLinearGroup (Fin 2) K) * tvSL = 1 := by
  apply Subtype.ext
  change (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K) * !![1, 0; 1, 1] = 1
  rw [← transvection_eq_fin_two,
    Matrix.transvection_mul_transvection_same (1 : Fin 2) 0 (by decide) (1 : K) (1 : K)]
  rw [show (1 : K) + 1 = 0 from CharTwo.add_self_eq_zero 1, Matrix.transvection_zero]

private theorem exists_orderOf_eq_card_add_one_tvSL_conj_eq_inv [Finite K] :
    ∃ S : Matrix.SpecialLinearGroup (Fin 2) K, orderOf S = Nat.card K + 1 ∧
      tvSL * S * tvSL = S⁻¹ := by
  obtain ⟨S, hS, hrel⟩ :=
    CFSG.ClassicalGroups.SpecialLinear.exists_orderOf_eq_card_add_one_conj_eq_inv (K := K)
  refine ⟨S, hS, Subtype.ext ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  change (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K) * _ * !![1, 0; 1, 1] = _
  rw [← transvection_eq_fin_two]
  exact hrel

private theorem conj_omega_of_det_eq_one (c : K) {M : Matrix (Fin 2) (Fin 2) K}
    (hM : M.det = 1) : Mᵀ * !![0, c; c, 0] * M = !![0, c; c, 0] := by
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by rwa [Matrix.det_fin_two] at hM
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (c * M 0 0 * M 1 0) * h2
  · linear_combination c * hdet + (c * M 0 1 * M 1 0) * h2
  · linear_combination c * hdet + (c * M 0 1 * M 1 0) * h2
  · linear_combination (c * M 0 1 * M 1 1) * h2

private def sl2Coe : Matrix.SpecialLinearGroup (Fin 2) K →* Matrix (Fin 2) (Fin 2) K where
  toFun S := (S : Matrix (Fin 2) (Fin 2) K)
  map_one' := Matrix.SpecialLinearGroup.coe_one
  map_mul' := Matrix.SpecialLinearGroup.coe_mul

private theorem sl2Coe_injective : Function.Injective (sl2Coe (K := K)) :=
  fun _ _ h => Subtype.ext h

open scoped Kronecker in
private def sl2Kron : Matrix.SpecialLinearGroup (Fin 2) K →*
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K where
  toFun S := (S : Matrix (Fin 2) (Fin 2) K) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) K)
  map_one' := by rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_kronecker_one]
  map_mul' S S' := by
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one]

open scoped Kronecker in
private theorem sl2Kron_injective : Function.Injective (sl2Kron (K := K)) := fun S S' h => by
  apply Subtype.ext
  ext i j
  have := congrFun (congrFun h (i, 0)) (j, 0)
  simpa [sl2Kron, Matrix.kroneckerMap_apply] using this

open scoped Kronecker in
private theorem sl2Kron_apply (S : Matrix.SpecialLinearGroup (Fin 2) K) :
    sl2Kron S = (S : Matrix (Fin 2) (Fin 2) K) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) K) := rfl

private theorem sl2Kron_apply_apply (S : Matrix.SpecialLinearGroup (Fin 2) K)
    (i j i' j' : Fin 2) : sl2Kron S (i, j) (i', j') =
      (S : Matrix (Fin 2) (Fin 2) K) i i' * (1 : Matrix (Fin 2) (Fin 2) K) j j' := rfl

open scoped Kronecker in
private theorem sl2Kron_conj (c : K) (S : Matrix.SpecialLinearGroup (Fin 2) K) :
    (sl2Kron S)ᵀ * (!![0, 1; 1, 0] ⊗ₖ !![0, c; c, 0]) * sl2Kron S =
      !![0, 1; 1, 0] ⊗ₖ !![0, c; c, 0] := by
  have h := conj_omega_of_det_eq_one (1 : K) S.2
  rw [sl2Kron_apply, ← Matrix.kroneckerMap_transpose, Matrix.transpose_one,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, h]

end SL2

section Assembly

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem exists_isometry_inv_conj_of_embed {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {J : Matrix ι ι K} (hJ : Jᵀ = J) {u : GL ι K}
    (hu : (u : Matrix ι ι K)ᵀ * J * (u : Matrix ι ι K) = J) (hu2 : u * u = 1)
    {A : Matrix ι κ K} {G H U : Matrix κ κ K} (hG : Aᵀ * J * A = G) (hGH : G * H = 1)
    (hHG : H * G = 1) (hUA : (u : Matrix ι ι K) * A = A * U)
    (Φ : Matrix.SpecialLinearGroup (Fin 2) K →* Matrix κ κ K)
    (hΦG : ∀ S, (Φ S)ᵀ * G * Φ S = G) (hΦinj : Function.Injective Φ) (hΦT : Φ tvSL = U) :
    ∃ s : GL ι K, orderOf s = Nat.card K + 1 ∧
      (s : Matrix ι ι K)ᵀ * J * (s : Matrix ι ι K) = J ∧ u⁻¹ * s * u = s⁻¹ := by
  obtain ⟨S, hSord, hSrel⟩ := exists_orderOf_eq_card_add_one_tvSL_conj_eq_inv (K := K)
  have hBA : (H * Aᵀ * J) * A = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Aᵀ J A, hG, hHG]
  have hu2' : (u : Matrix ι ι K) * (u : Matrix ι ι K) = 1 := by
    simpa using congrArg (fun x : GL ι K => (x : Matrix ι ι K)) hu2
  have hU2 : U * U = 1 := by
    rw [← hΦT, ← map_mul, tvSL_mul_self, map_one]
  have hBu := proj_mul_involution hJ hu hu2' hG hGH hHG hU2 hUA
  refine ⟨embedHom hBA Φ S, ?_, ?_, ?_⟩
  · rw [← hSord]
    exact orderOf_injective _ (embedHom_injective hBA hΦinj) S
  · rw [coe_embedHom]
    exact embedMat_isometry hJ hG hGH hHG (hΦG S)
  · have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    rw [huinv, ← map_inv]
    apply Units.ext
    rw [coe_embedHom]
    simp only [Units.val_mul]
    rw [coe_embedHom, embedMat_conj hu2' hU2 hUA hBu, ← hΦT, ← map_mul, ← map_mul, hSrel]

end Assembly

section Bil

variable {K : Type} [Field K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]

private def colVec {κ : Type} (A : Matrix ι κ K) (i : κ) : ι → K := fun r => A r i

private theorem gram_apply {κ : Type} (A : Matrix ι κ K) (J : Matrix ι ι K) (i j : κ) :
    (Aᵀ * J * A) i j = colVec A i ⬝ᵥ J *ᵥ colVec A j := by
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, colVec, Finset.sum_mul, Finset.mul_sum,
    mul_assoc]
  rw [Finset.sum_comm]

variable {J : Matrix ι ι K} {u : Matrix ι ι K}

private theorem bil_symm (hJ : Jᵀ = J) (v w : ι → K) : v ⬝ᵥ J *ᵥ w = w ⬝ᵥ J *ᵥ v := by
  calc v ⬝ᵥ J *ᵥ w = (v ᵥ* J) ⬝ᵥ w := Matrix.dotProduct_mulVec v J w
    _ = (J *ᵥ v) ⬝ᵥ w := by rw [← hJ, Matrix.vecMul_transpose, hJ]
    _ = w ⬝ᵥ J *ᵥ v := dotProduct_comm _ _

private theorem J_mul_sub_one (hu : uᵀ * J * u = J) (hu2 : u * u = 1) :
    J * (u - 1) = (u - 1)ᵀ * J := by
  have hJu : J * u = uᵀ * J := by
    calc J * u = (uᵀ * J * u) * u := by rw [hu]
      _ = uᵀ * J := by rw [Matrix.mul_assoc, hu2, Matrix.mul_one]
  rw [Matrix.mul_sub, Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, hJu,
    Matrix.mul_one, Matrix.one_mul]

private theorem bil_sub_one_right (hu : uᵀ * J * u = J) (hu2 : u * u = 1) (v w : ι → K) :
    v ⬝ᵥ J *ᵥ ((u - 1) *ᵥ w) = ((u - 1) *ᵥ v) ⬝ᵥ J *ᵥ w := by
  rw [Matrix.mulVec_mulVec, J_mul_sub_one hu hu2, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

private theorem sub_one_mul_self_eq_zero (hu2 : u * u = 1) : (u - 1) * (u - 1) = 0 := by
  calc (u - 1) * (u - 1) = (1 - u) + (1 - u) := by
        simp only [Matrix.sub_mul, Matrix.mul_sub, hu2, Matrix.mul_one, Matrix.one_mul]
        abel
    _ = (2 : K) • (1 - u) := (two_smul K _).symm
    _ = 0 := by rw [CharTwo.two_eq_zero, zero_smul]

private theorem exists_mulVec_ne_zero {N : Matrix ι ι K} (hN : N ≠ 0) :
    ∃ v : ι → K, N *ᵥ v ≠ 0 := by
  by_contra h
  push Not at h
  exact hN (by
    ext i j
    simpa [Matrix.mulVec_single_one] using congrFun (h (Pi.single j 1)) i)

private theorem mulVec_eq_add_sub_one (u : Matrix ι ι K) (v : ι → K) :
    u *ᵥ v = v + (u - 1) *ᵥ v := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel

private theorem exists_pair {N : Matrix ι ι K} (hN2 : N * N = 0) (hJ2 : J * J = 1)
    (hN0 : N ≠ 0) : ∃ x y : ι → K, x ⬝ᵥ J *ᵥ y = 0 ∧ x ⬝ᵥ J *ᵥ (N *ᵥ y) ≠ 0 := by
  obtain ⟨y, hy⟩ := exists_mulVec_ne_zero hN0
  have hz : J *ᵥ (N *ᵥ y) ≠ 0 := by
    intro h
    apply hy
    calc N *ᵥ y = (J * J) *ᵥ (N *ᵥ y) := by rw [hJ2, Matrix.one_mulVec]
      _ = J *ᵥ (J *ᵥ (N *ᵥ y)) := by rw [← Matrix.mulVec_mulVec]
      _ = 0 := by rw [h, Matrix.mulVec_zero]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
  set x : ι → K := Pi.single i 1 with hx
  set c : K := x ⬝ᵥ J *ᵥ (N *ᵥ y) with hc
  have hc0 : c ≠ 0 := by
    rw [hc, hx, single_one_dotProduct]
    simpa using hi
  set e : K := x ⬝ᵥ J *ᵥ y with he
  set y₁ : ι → K := y + (e / c) • (N *ᵥ y) with hy₁
  have hNy₁ : N *ᵥ y₁ = N *ᵥ y := by
    rw [hy₁, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hN2,
      Matrix.zero_mulVec, smul_zero, add_zero]
  refine ⟨x, y₁, ?_, by rw [hNy₁]; exact hc0⟩
  rw [hy₁, Matrix.mulVec_add, dotProduct_add, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
    ← he, ← hc, div_mul_cancel₀ _ hc0]
  exact CharTwo.add_self_eq_zero e

end Bil

section Cases

variable {K : Type} [Field K] [Finite K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]
  {J : Matrix ι ι K}

private theorem exists_inv_conj_of_bil_ne_zero (hJ : Jᵀ = J)
    (hJa : ∀ v : ι → K, v ⬝ᵥ J *ᵥ v = 0) {u : GL ι K}
    (hu : (u : Matrix ι ι K)ᵀ * J * (u : Matrix ι ι K) = J) (hu2 : u * u = 1) {v : ι → K}
    (hv : v ⬝ᵥ J *ᵥ (((u : Matrix ι ι K) - 1) *ᵥ v) ≠ 0) :
    ∃ s : GL ι K, orderOf s = Nat.card K + 1 ∧
      (s : Matrix ι ι K)ᵀ * J * (s : Matrix ι ι K) = J ∧ u⁻¹ * s * u = s⁻¹ := by
  have hu2' : (u : Matrix ι ι K) * (u : Matrix ι ι K) = 1 := by
    simpa using congrArg (fun x : GL ι K => (x : Matrix ι ι K)) hu2
  set Um : Matrix ι ι K := (u : Matrix ι ι K) with hUm
  set w : ι → K := (Um - 1) *ᵥ v with hw
  set c : K := v ⬝ᵥ J *ᵥ w with hc
  have hc0 : c ≠ 0 := hv
  have hNw : (Um - 1) *ᵥ w = 0 := by
    rw [hw, Matrix.mulVec_mulVec, sub_one_mul_self_eq_zero hu2', Matrix.zero_mulVec]
  let A : Matrix ι (Fin 2) K := Matrix.of fun r k => ![v, w] k r
  have hcol0 : colVec A 0 = v := rfl
  have hcol1 : colVec A 1 = w := rfl
  have h0 : Um *ᵥ v = v + w := mulVec_eq_add_sub_one Um v
  have h1 : Um *ᵥ w = w := by rw [mulVec_eq_add_sub_one Um w, hNw, add_zero]
  refine exists_isometry_inv_conj_of_embed hJ hu hu2 (A := A) (G := !![0, c; c, 0])
    (H := !![0, c⁻¹; c⁻¹, 0]) (U := !![1, 0; 1, 1]) ?_ ?_ ?_ ?_ sl2Coe
    (fun S => conj_omega_of_det_eq_one c S.2) sl2Coe_injective rfl
  · ext i j
    rw [gram_apply]
    fin_cases i <;> fin_cases j <;> simp [hcol0, hcol1, hJa]
    · exact hc.symm
    · exact (bil_symm hJ w v).trans hc.symm
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc0]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc0]
  · ext r k
    fin_cases k
    · change (Um * A) r 0 = (A * (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K)) r 0
      rw [show (Um * A) r 0 = (Um *ᵥ colVec A 0) r from rfl, hcol0, h0]
      simp [Matrix.mul_apply, Fin.sum_univ_two, A]
    · change (Um * A) r 1 = (A * (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K)) r 1
      rw [show (Um * A) r 1 = (Um *ᵥ colVec A 1) r from rfl, hcol1, h1]
      simp [Matrix.mul_apply, Fin.sum_univ_two, A]

open scoped Kronecker in
private theorem exists_inv_conj_of_forall_bil_eq_zero (hJ : Jᵀ = J)
    (hJa : ∀ v : ι → K, v ⬝ᵥ J *ᵥ v = 0) {u : GL ι K}
    (hu : (u : Matrix ι ι K)ᵀ * J * (u : Matrix ι ι K) = J) (hu2 : u * u = 1)
    (hN : ∀ v : ι → K, v ⬝ᵥ J *ᵥ (((u : Matrix ι ι K) - 1) *ᵥ v) = 0) {x y : ι → K}
    (hxy : x ⬝ᵥ J *ᵥ y = 0) (hc : x ⬝ᵥ J *ᵥ (((u : Matrix ι ι K) - 1) *ᵥ y) ≠ 0) :
    ∃ s : GL ι K, orderOf s = Nat.card K + 1 ∧
      (s : Matrix ι ι K)ᵀ * J * (s : Matrix ι ι K) = J ∧ u⁻¹ * s * u = s⁻¹ := by
  have hu2' : (u : Matrix ι ι K) * (u : Matrix ι ι K) = 1 := by
    simpa using congrArg (fun x : GL ι K => (x : Matrix ι ι K)) hu2
  set Um : Matrix ι ι K := (u : Matrix ι ι K) with hUm
  set N : Matrix ι ι K := Um - 1 with hNdef
  have hN2 : N * N = 0 := sub_one_mul_self_eq_zero hu2'
  set c : K := x ⬝ᵥ J *ᵥ (N *ᵥ y) with hcdef
  have hsymm := bil_symm hJ
  have hNN : ∀ v : ι → K, N *ᵥ (N *ᵥ v) = 0 := fun v => by
    rw [Matrix.mulVec_mulVec, hN2, Matrix.zero_mulVec]
  have hxx : x ⬝ᵥ J *ᵥ x = 0 := hJa x
  have hxNx : x ⬝ᵥ J *ᵥ (N *ᵥ x) = 0 := hN x
  have hxNy : x ⬝ᵥ J *ᵥ (N *ᵥ y) = c := rfl
  have hyx : y ⬝ᵥ J *ᵥ x = 0 := (hsymm y x).trans hxy
  have hyy : y ⬝ᵥ J *ᵥ y = 0 := hJa y
  have hyNx : y ⬝ᵥ J *ᵥ (N *ᵥ x) = c := by
    rw [bil_sub_one_right hu hu2' y x]
    exact (hsymm _ _).trans hxNy
  have hyNy : y ⬝ᵥ J *ᵥ (N *ᵥ y) = 0 := hN y
  have hNxx : (N *ᵥ x) ⬝ᵥ J *ᵥ x = 0 := (hsymm _ _).trans hxNx
  have hNxy : (N *ᵥ x) ⬝ᵥ J *ᵥ y = c := (hsymm _ _).trans hyNx
  have hNxNx : (N *ᵥ x) ⬝ᵥ J *ᵥ (N *ᵥ x) = 0 := hJa _
  have hNxNy : (N *ᵥ x) ⬝ᵥ J *ᵥ (N *ᵥ y) = 0 := by
    rw [← bil_sub_one_right hu hu2' x (N *ᵥ y), hNN, Matrix.mulVec_zero, dotProduct_zero]
  have hNyx : (N *ᵥ y) ⬝ᵥ J *ᵥ x = c := (hsymm _ _).trans hxNy
  have hNyy : (N *ᵥ y) ⬝ᵥ J *ᵥ y = 0 := (hsymm _ _).trans hyNy
  have hNyNx : (N *ᵥ y) ⬝ᵥ J *ᵥ (N *ᵥ x) = 0 := (hsymm _ _).trans hNxNy
  have hNyNy : (N *ᵥ y) ⬝ᵥ J *ᵥ (N *ᵥ y) = 0 := hJa _
  let A : Matrix ι (Fin 2 × Fin 2) K :=
    Matrix.of fun r p => ![![x, y], ![N *ᵥ x, N *ᵥ y]] p.1 p.2 r
  have hc00 : colVec A (0, 0) = x := rfl
  have hc01 : colVec A (0, 1) = y := rfl
  have hc10 : colVec A (1, 0) = N *ᵥ x := rfl
  have hc11 : colVec A (1, 1) = N *ᵥ y := rfl
  have hG : Aᵀ * J * A = !![0, 1; 1, 0] ⊗ₖ !![0, c; c, 0] := by
    ext ⟨i, j⟩ ⟨i', j'⟩
    rw [gram_apply]
    fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
      simp [Matrix.kroneckerMap_apply, hc00, hc01, hc10, hc11, hxx, hxy, hxNx, hxNy, hyx, hyy,
        hyNx, hyNy, hNxx, hNxy, hNxNx, hNxNy, hNyx, hNyy, hNyNx, hNyNy, -Matrix.mulVec_mulVec]
  have hω : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) * !![0, 1; 1, 0] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hs : (!![0, c; c, 0] : Matrix (Fin 2) (Fin 2) K) * !![0, c⁻¹; c⁻¹, 0] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc]
  have hs' : (!![0, c⁻¹; c⁻¹, 0] : Matrix (Fin 2) (Fin 2) K) * !![0, c; c, 0] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc]
  have hGH : (!![0, 1; 1, 0] ⊗ₖ !![0, c; c, 0] : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K) *
      (!![0, 1; 1, 0] ⊗ₖ !![0, c⁻¹; c⁻¹, 0]) = 1 := by
    rw [← Matrix.mul_kronecker_mul, hω, hs, Matrix.one_kronecker_one]
  have hHG : (!![0, 1; 1, 0] ⊗ₖ !![0, c⁻¹; c⁻¹, 0] : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K) *
      (!![0, 1; 1, 0] ⊗ₖ !![0, c; c, 0]) = 1 := by
    rw [← Matrix.mul_kronecker_mul, hω, hs', Matrix.one_kronecker_one]
  have hUx : Um *ᵥ x = x + N *ᵥ x := mulVec_eq_add_sub_one Um x
  have hUy : Um *ᵥ y = y + N *ᵥ y := mulVec_eq_add_sub_one Um y
  have hUNx : Um *ᵥ (N *ᵥ x) = N *ᵥ x := by
    rw [mulVec_eq_add_sub_one Um (N *ᵥ x)]
    change N *ᵥ x + N *ᵥ (N *ᵥ x) = N *ᵥ x
    rw [hNN, add_zero]
  have hUNy : Um *ᵥ (N *ᵥ y) = N *ᵥ y := by
    rw [mulVec_eq_add_sub_one Um (N *ᵥ y)]
    change N *ᵥ y + N *ᵥ (N *ᵥ y) = N *ᵥ y
    rw [hNN, add_zero]
  have hUA : Um * A = A * sl2Kron tvSL := by
    ext r ⟨i, j⟩
    fin_cases i <;> fin_cases j
    · change (Um * A) r (0, 0) = (A * sl2Kron (tvSL (K := K))) r (0, 0)
      rw [show (Um * A) r (0, 0) = (Um *ᵥ colVec A (0, 0)) r from rfl, hc00, hUx]
      simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, sl2Kron_apply_apply, A,
        Matrix.one_apply, tvSL_coe]
    · change (Um * A) r (0, 1) = (A * sl2Kron (tvSL (K := K))) r (0, 1)
      rw [show (Um * A) r (0, 1) = (Um *ᵥ colVec A (0, 1)) r from rfl, hc01, hUy]
      simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, sl2Kron_apply_apply, A,
        Matrix.one_apply, tvSL_coe]
    · change (Um * A) r (1, 0) = (A * sl2Kron (tvSL (K := K))) r (1, 0)
      rw [show (Um * A) r (1, 0) = (Um *ᵥ colVec A (1, 0)) r from rfl, hc10, hUNx]
      simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, sl2Kron_apply_apply, A,
        Matrix.one_apply, tvSL_coe]
    · change (Um * A) r (1, 1) = (A * sl2Kron (tvSL (K := K))) r (1, 1)
      rw [show (Um * A) r (1, 1) = (Um *ᵥ colVec A (1, 1)) r from rfl, hc11, hUNy]
      simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, sl2Kron_apply_apply, A,
        Matrix.one_apply, tvSL_coe]
  exact exists_isometry_inv_conj_of_embed hJ hu hu2 (A := A)
    (G := !![0, 1; 1, 0] ⊗ₖ !![0, c; c, 0]) (H := !![0, 1; 1, 0] ⊗ₖ !![0, c⁻¹; c⁻¹, 0])
    (U := sl2Kron tvSL) hG hGH hHG hUA sl2Kron (fun S => sl2Kron_conj c S) sl2Kron_injective rfl

private theorem exists_inv_conj_of_involution (hJ : Jᵀ = J)
    (hJa : ∀ v : ι → K, v ⬝ᵥ J *ᵥ v = 0) (hJ2 : J * J = 1) {u : GL ι K}
    (hu : (u : Matrix ι ι K)ᵀ * J * (u : Matrix ι ι K) = J) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ s : GL ι K, orderOf s = Nat.card K + 1 ∧
      (s : Matrix ι ι K)ᵀ * J * (s : Matrix ι ι K) = J ∧ u⁻¹ * s * u = s⁻¹ := by
  by_cases h : ∃ v : ι → K, v ⬝ᵥ J *ᵥ (((u : Matrix ι ι K) - 1) *ᵥ v) ≠ 0
  · obtain ⟨v, hv⟩ := h
    exact exists_inv_conj_of_bil_ne_zero hJ hJa hu hu2 hv
  · push Not at h
    have hu2' : (u : Matrix ι ι K) * (u : Matrix ι ι K) = 1 := by
      simpa using congrArg (fun x : GL ι K => (x : Matrix ι ι K)) hu2
    have hN0 : ((u : Matrix ι ι K) - 1) ≠ 0 := fun h0 => hu1 (Units.ext (sub_eq_zero.mp h0))
    obtain ⟨x, y, hxy, hc⟩ := exists_pair (sub_one_mul_self_eq_zero hu2') hJ2 hN0
    exact exists_inv_conj_of_forall_bil_eq_zero hJ hJa hu hu2 h hxy hc

end Cases

section StatedSp

variable {K : Type} [Field K] [CharP K 2] {m : ℕ}

private theorem neg_one_matrix_eq : (-1 : Matrix (Fin m) (Fin m) K) = 1 := by
  ext i j
  simp [Matrix.one_apply, CharTwo.neg_eq]

private theorem fromBlocks_transpose_eq :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)ᵀ =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  rw [Matrix.fromBlocks_transpose]
  simp [neg_one_matrix_eq]

private theorem fromBlocks_mul_self :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
      Matrix.fromBlocks 0 1 (-1) 0 = 1 := by
  rw [Matrix.fromBlocks_multiply]
  simp [neg_one_matrix_eq]

private theorem fromBlocks_alternating (v : Fin m ⊕ Fin m → K) :
    v ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v = 0 := by
  simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.one_apply, mul_comm]

end StatedSp

end InvolutionInverts

section Main

open CFSG.Open InvolutionInverts

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}

theorem exists_inv_conj_of_sq_eq_one_statedSp {u : GL (Fin m ⊕ Fin m) K}
    (hu : u ∈ StatedSp m K) (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) :
    ∃ s ∈ StatedSp m K, orderOf s = Nat.card K + 1 ∧ u⁻¹ * s * u = s⁻¹ := by
  have huJ := StatedAPI.mem_statedSp_iff.1 hu
  obtain ⟨s, hs, hsJ, hrel⟩ := exists_inv_conj_of_involution (K := K)
    (J := (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K))
    fromBlocks_transpose_eq fromBlocks_alternating fromBlocks_mul_self huJ
    (by rwa [pow_two] at hu2) hu1
  exact ⟨s, StatedAPI.mem_statedSp_iff.2 hsJ, hs, hrel⟩

private noncomputable def projEquiv : StatedProj (StatedSp m K) ≃* StatedSp m K :=
  (QuotientGroup.quotientMulEquivOfEq StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot).trans
    QuotientGroup.quotientBot

theorem exists_inv_conj_statedProj_statedSp {d : StatedProj (StatedSp m K)}
    (hd : orderOf d = 2) :
    ∃ τ : StatedProj (StatedSp m K), orderOf τ = Nat.card K + 1 ∧ d⁻¹ * τ * d = τ⁻¹ := by
  let e := projEquiv (m := m) (K := K)
  have hd' : orderOf (e d) = 2 := by rw [MulEquiv.orderOf_eq, hd]
  have hu2 : ((e d : StatedSp m K) : GL (Fin m ⊕ Fin m) K) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (e d)
    rw [hd'] at h
    simpa using congrArg (fun x : StatedSp m K => (x : GL (Fin m ⊕ Fin m) K)) h
  have hu1 : ((e d : StatedSp m K) : GL (Fin m ⊕ Fin m) K) ≠ 1 := by
    intro h
    have h1 : e d = 1 := Subtype.ext h
    rw [h1, orderOf_one] at hd'
    omega
  obtain ⟨s, hsmem, hsord, hsrel⟩ := exists_inv_conj_of_sq_eq_one_statedSp (e d).2 hu2 hu1
  let S : StatedSp m K := ⟨s, hsmem⟩
  refine ⟨e.symm S, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, ← hsord]
    exact (Subgroup.orderOf_coe S).symm
  · apply e.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, map_inv]
    apply Subtype.ext
    simpa using hsrel

theorem exists_inv_conj_of_lieModel_psp_of_orderOf_eq_two {Y : Type} [Group Y] {m x : ℕ}
    (h : CFSG.Blueprint.LieModel Y .PSp m 2 x) {d : Y} (hd : orderOf d = 2) :
    ∃ τ : Y, orderOf τ = 2 ^ x + 1 ∧ d⁻¹ * τ * d = τ⁻¹ := by
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  letI : Field K := hKf
  haveI : Finite K := hKfin
  haveI : CharP K 2 := CFSG.Quasithin.R3c.charP_two_of_natCard_eq_two_pow hKcard
  have hd' : orderOf (e d) = 2 := by rw [MulEquiv.orderOf_eq, hd]
  obtain ⟨τ, hτ, hrel⟩ := exists_inv_conj_statedProj_statedSp (d := e d) hd'
  refine ⟨e.symm τ, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, hτ, hKcard]
  · have h' := congrArg e.symm hrel
    simpa using h'

end Main

end CFSG.ClassicalGroups.Symplectic
