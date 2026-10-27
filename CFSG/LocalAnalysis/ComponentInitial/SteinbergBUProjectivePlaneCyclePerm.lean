module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXClassicalTorus
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXCentralLift

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open Matrix Equiv CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.GorensteinLyons

variable {K : Type*} [Field K]

theorem permMatrix_one_eq (n : ℕ) : permMatrix n K 1 = 1 := by
  ext a b
  rw [permMatrix_apply, Perm.one_apply, one_apply]

theorem permMatrix_pow_eq (n : ℕ) (w : Perm (Fin n)) (k : ℕ) :
    permMatrix n K w ^ k = permMatrix n K (w ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, permMatrix_one_eq]
  | succ k ih => rw [pow_succ, ih, permMatrix_mul_permMatrix, pow_succ]

@[expose] noncomputable def cycleGL (p : ℕ) (K : Type*) [Field K] : GL (Fin p) K where
  val := permMatrix p K (finRotate p)
  inv := permMatrix p K (finRotate p)⁻¹
  val_inv := by rw [permMatrix_mul_permMatrix, mul_inv_cancel, permMatrix_one_eq]
  inv_val := by rw [permMatrix_mul_permMatrix, inv_mul_cancel, permMatrix_one_eq]

theorem coe_cycleGL (p : ℕ) (K : Type*) [Field K] :
    (cycleGL p K : Matrix (Fin p) (Fin p) K) = permMatrix p K (finRotate p) :=
  rfl

variable {p : ℕ}

theorem finRotate_pow_self : finRotate p ^ p = 1 := by
  rcases p with _ | _ | n
  · exact pow_zero _
  · show finRotate 1 ^ 1 = 1
    exact Subsingleton.elim _ _
  · have h := (isCycle_finRotate (n := n)).orderOf
    rw [support_finRotate, Finset.card_univ, Fintype.card_fin] at h
    have h1 := pow_orderOf_eq_one (finRotate (n + 2))
    rwa [h] at h1

theorem cycleGL_pow : cycleGL p K ^ p = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_cycleGL, permMatrix_pow_eq, finRotate_pow_self,
    permMatrix_one_eq, Units.val_one]

theorem det_cycleGL (hp : Odd p) : (cycleGL p K : Matrix (Fin p) (Fin p) K).det = 1 := by
  rw [coe_cycleGL, det_permMatrix, sign_finRotate]
  obtain ⟨k, rfl⟩ := hp
  rw [Nat.add_sub_cancel, (even_two_mul k).neg_one_pow, Units.val_one, Int.cast_one]

theorem pow_finRotate {ζ : K} (hζ : ζ ^ p = 1) (b : Fin p) :
    ζ ^ ((finRotate p b : Fin p) : ℕ) = ζ * ζ ^ (b : ℕ) := by
  rcases p with _ | n
  · exact b.elim0
  · by_cases hb : b = Fin.last n
    · rw [hb, finRotate_last, Fin.val_zero, pow_zero, Fin.val_last, ← pow_succ', hζ]
    · rw [coe_finRotate_of_ne_last hb, pow_succ']

theorem cycleGL_mul_diagonal {ζ : K} (hζ : ζ ^ p = 1) :
    (cycleGL p K : Matrix (Fin p) (Fin p) K) * diagonal (fun i : Fin p => ζ ^ (i : ℕ)) =
      ζ⁻¹ • (diagonal (fun i : Fin p => ζ ^ (i : ℕ)) * cycleGL p K) := by
  rw [coe_cycleGL, permMatrix_mul_diagonal', ← Matrix.smul_mul, ← diagonal_smul]
  congr 2
  funext a
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (Fin.pos a).ne'] at hζ
    exact zero_ne_one hζ
  have h := pow_finRotate hζ ((finRotate p)⁻¹ a)
  rw [show (finRotate p) ((finRotate p)⁻¹ a) = a from (finRotate p).apply_symm_apply a] at h
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h, inv_mul_cancel_left₀ hζ0]

theorem cycleGL_map {r f : ℕ} (h : UnitaryFieldData r f K) :
    (cycleGL p K : Matrix (Fin p) (Fin p) K).map h.bar = cycleGL p K := by
  ext a b
  simp only [map_apply, coe_cycleGL, permMatrix_apply]
  split_ifs <;> simp

theorem cycleGL_unitary {r f : ℕ} (h : UnitaryFieldData r f K) :
    ((cycleGL p K : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ * cycleGL p K = 1 := by
  rw [cycleGL_map, coe_cycleGL, transpose_permMatrix_mul_self]

end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
