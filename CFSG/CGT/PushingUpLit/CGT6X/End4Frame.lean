module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.End4

open Matrix

variable {K : Type*} [Field K]

@[expose] def fc : Fin 3 → K := ![1, 1, 1]

@[expose] def fu (s : K) : Fin 3 → K := ![1, s, 1 + s]

@[expose] def fv (s : K) : Fin 3 → K := ![1, 1 + s, s]

@[expose] def e0 : Matrix (Fin 3) (Fin 3) K := vecMulVec fc fc

@[expose] def e1 (s : K) : Matrix (Fin 3) (Fin 3) K := vecMulVec (fu s) (fv s)

@[expose] def e2 (s : K) : Matrix (Fin 3) (Fin 3) K := vecMulVec (fv s) (fu s)

@[expose] def tm (s x y z : K) : Matrix (Fin 3) (Fin 3) K := x • e0 + y • e1 s + z • e2 s

@[expose] def wm (s : K) : Matrix (Fin 3) (Fin 3) K :=
  vecMulVec (fu s) fc + vecMulVec fc (fv s) + vecMulVec (fv s) (fu s)

section CharTwo

variable [CharP K 2] (s : K)

theorem two_eq_zero' : (2 : K) = 0 := CharP.cast_eq_zero K 2

theorem cc : fc ⬝ᵥ fc = (1 : K) := by
  have h2 := two_eq_zero' (K := K)
  simp [fc, dotProduct, Fin.sum_univ_three]
  linear_combination h2

theorem cu : fc ⬝ᵥ fu s = 0 := by
  have h2 := two_eq_zero' (K := K)
  simp [fc, fu, dotProduct, Fin.sum_univ_three]
  linear_combination (1 + s) * h2

theorem cv : fc ⬝ᵥ fv s = 0 := by
  have h2 := two_eq_zero' (K := K)
  simp [fc, fv, dotProduct, Fin.sum_univ_three]
  linear_combination (1 + s) * h2

theorem uu : fu s ⬝ᵥ fu s = 0 := by
  have h2 := two_eq_zero' (K := K)
  simp [fu, dotProduct, Fin.sum_univ_three]
  linear_combination (1 + s + s ^ 2) * h2

theorem vv : fv s ⬝ᵥ fv s = 0 := by
  have h2 := two_eq_zero' (K := K)
  simp [fv, dotProduct, Fin.sum_univ_three]
  linear_combination (1 + s + s ^ 2) * h2

theorem uv : fu s ⬝ᵥ fv s = 1 := by
  have h2 := two_eq_zero' (K := K)
  simp [fu, fv, dotProduct, Fin.sum_univ_three]
  linear_combination (s + s ^ 2) * h2

theorem vc : fv s ⬝ᵥ fc = 0 := by rw [dotProduct_comm]; exact cv s

theorem uc : fu s ⬝ᵥ fc = 0 := by rw [dotProduct_comm]; exact cu s

theorem vu : fv s ⬝ᵥ fu s = 1 := by rw [dotProduct_comm]; exact uv s

theorem complete : e0 + e1 s + e2 s = (1 : Matrix (Fin 3) (Fin 3) K) := by
  have h2 := two_eq_zero' (K := K)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e0, e1, e2, fc, fu, fv] <;>
    first | linear_combination h2 | linear_combination (1 + s) * h2 |
      linear_combination (s + s ^ 2) * h2 | linear_combination (1 + s + s ^ 2) * h2

theorem e00 : e0 * e0 = (e0 : Matrix (Fin 3) (Fin 3) K) := by
  rw [e0, vecMulVec_mul_vecMulVec, cc, one_smul]

theorem e01 : e0 * e1 s = (0 : Matrix (Fin 3) (Fin 3) K) := by
  rw [e0, e1, vecMulVec_mul_vecMulVec, cu, zero_smul, vecMulVec_zero]

theorem e02 : e0 * e2 s = (0 : Matrix (Fin 3) (Fin 3) K) := by
  rw [e0, e2, vecMulVec_mul_vecMulVec, cv, zero_smul, vecMulVec_zero]

theorem e10 : e1 s * e0 = (0 : Matrix (Fin 3) (Fin 3) K) := by
  rw [e0, e1, vecMulVec_mul_vecMulVec, vc, zero_smul, vecMulVec_zero]

theorem e11 : e1 s * e1 s = (e1 s : Matrix (Fin 3) (Fin 3) K) := by
  rw [e1, vecMulVec_mul_vecMulVec, vu, one_smul]

theorem e12 : e1 s * e2 s = (0 : Matrix (Fin 3) (Fin 3) K) := by
  rw [e1, e2, vecMulVec_mul_vecMulVec, vv, zero_smul, vecMulVec_zero]

theorem e20 : e2 s * e0 = (0 : Matrix (Fin 3) (Fin 3) K) := by
  rw [e0, e2, vecMulVec_mul_vecMulVec, uc, zero_smul, vecMulVec_zero]

theorem e21 : e2 s * e1 s = (0 : Matrix (Fin 3) (Fin 3) K) := by
  rw [e1, e2, vecMulVec_mul_vecMulVec, uu, zero_smul, vecMulVec_zero]

theorem e22 : e2 s * e2 s = (e2 s : Matrix (Fin 3) (Fin 3) K) := by
  rw [e2, vecMulVec_mul_vecMulVec, uv, one_smul]

theorem tm_mul (x y z x' y' z' : K) :
    tm s x y z * tm s x' y' z' = tm s (x * x') (y * y') (z * z') := by
  simp only [tm, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, e00, e01, e02, e10, e11, e12,
    e20, e21, e22 (s := s), smul_zero, add_zero, zero_add, smul_smul]
  module

theorem tm_one : tm s 1 1 1 = (1 : Matrix (Fin 3) (Fin 3) K) := by
  simp only [tm, one_smul]; exact complete s

omit [CharP K 2] in
theorem tm_transpose (x y z : K) : (tm s x y z)ᵀ = tm s x z y := by
  have h0 : (e0 : Matrix (Fin 3) (Fin 3) K)ᵀ = e0 := by rw [e0, transpose_vecMulVec]
  have h1 : (e1 s)ᵀ = e2 s := by rw [e1, e2, transpose_vecMulVec]
  have h2 : (e2 s)ᵀ = e1 s := by rw [e1, e2, transpose_vecMulVec]
  simp only [tm, transpose_add, transpose_smul, h0, h1, h2]
  module

omit [CharP K 2] in
theorem det_one_add_smul_vecMulVec (a b : Fin 3 → K) (t : K) (h : b ⬝ᵥ a = 1) :
    (1 + t • vecMulVec a b : Matrix (Fin 3) (Fin 3) K).det = 1 + t := by
  have e : (t • vecMulVec a b : Matrix (Fin 3) (Fin 3) K) =
      replicateCol Unit (t • a) * replicateRow Unit b := by
    rw [← smul_vecMulVec, vecMulVec_eq (ι := Unit)]
  rw [e, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, h, smul_eq_mul, mul_one,
    add_comm]

theorem tm_x (x : K) : tm s x 1 1 = 1 + (x - 1) • e0 := by
  rw [tm, ← complete s]; module

theorem tm_y (y : K) : tm s 1 y 1 = 1 + (y - 1) • e1 s := by
  rw [tm, ← complete s]; module

theorem tm_z (z : K) : tm s 1 1 z = 1 + (z - 1) • e2 s := by
  rw [tm, ← complete s]; module

theorem det_tm (x y z : K) : (tm s x y z).det = x * y * z := by
  have h : tm s x y z = tm s x 1 1 * tm s 1 y 1 * tm s 1 1 z := by
    rw [tm_mul, tm_mul]; simp
  rw [h, det_mul, det_mul, tm_x, tm_y, tm_z, e0, e1, e2,
    det_one_add_smul_vecMulVec _ _ _ (by rw [cc]),
    det_one_add_smul_vecMulVec _ _ _ (vu s),
    det_one_add_smul_vecMulVec _ _ _ (uv s)]
  ring

theorem tm_eq_diag (x y : K) :
    tm s x y y = y • (1 : Matrix (Fin 3) (Fin 3) K) + (x - y) • e0 := by
  rw [tm, ← complete s]; module

theorem wm_tm (x y z : K) : wm s * tm s x y z = tm s y x z * wm s := by
  simp only [wm, tm, e0, e1, e2, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    vecMulVec_mul_vecMulVec, cc, cu, cv, uc, vc, uu, vv, uv, vu, smul_zero, zero_smul, one_smul,
    vecMulVec_zero, add_zero, zero_add]

theorem wm_sq : wm s * wm s = (1 : Matrix (Fin 3) (Fin 3) K) := by
  have h := complete s
  simp only [wm, add_mul, mul_add, vecMulVec_mul_vecMulVec, cc, cu, cv, uc, vc, uu, vv, uv, vu,
    zero_smul, one_smul, vecMulVec_zero, add_zero, zero_add]
  rw [← h, e0, e1, e2]

theorem tm_map (σ : K →+* K) (hσ : σ s = 1 + s) (x y z : K) :
    (tm s x y z).map σ = tm s (σ x) (σ z) (σ y) := by
  have h2 := two_eq_zero' (K := K)
  have hs2 : (1 : K) + (1 + s) = s := by linear_combination h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tm, e0, e1, e2, fc, fu, fv, hσ, hs2] <;> ring

omit [CharP K 2] in
theorem comm_e0 {A : Matrix (Fin 3) (Fin 3) K}
    (hr : ∀ i, A i 0 + A i 1 + A i 2 = 1) (hc : ∀ j, A 0 j + A 1 j + A 2 j = 1) :
    A * e0 = e0 * A := by
  have hfc : ∀ i, (fc : Fin 3 → K) i = 1 := fun i => by fin_cases i <;> rfl
  have h1 : A *ᵥ fc = fc := by
    ext i
    simp only [mulVec, dotProduct, Fin.sum_univ_three, hfc, mul_one]
    exact hr i
  have h2' : fc ᵥ* A = fc := by
    ext j
    simp only [vecMul, dotProduct, Fin.sum_univ_three, hfc, one_mul]
    exact hc j
  rw [e0, mul_vecMulVec, vecMulVec_mul, h1, h2']

theorem tm_comm {A : Matrix (Fin 3) (Fin 3) K}
    (hr : ∀ i, A i 0 + A i 1 + A i 2 = 1) (hc : ∀ j, A 0 j + A 1 j + A 2 j = 1) (x y : K) :
    A * tm s x y y = tm s x y y * A := by
  rw [tm_eq_diag, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, comm_e0 hr hc, mul_one, one_mul]

theorem tm_mul_inv (x y z : Kˣ) :
    tm s x y z * tm s (x⁻¹ : Kˣ) (y⁻¹ : Kˣ) (z⁻¹ : Kˣ) =
      (1 : Matrix (Fin 3) (Fin 3) K) := by
  rw [tm_mul]; simp [tm_one]

theorem tm_inv_mul (x y z : Kˣ) :
    tm s (x⁻¹ : Kˣ) (y⁻¹ : Kˣ) (z⁻¹ : Kˣ) * tm s x y z =
      (1 : Matrix (Fin 3) (Fin 3) K) := by
  rw [tm_mul]; simp [tm_one]

@[expose] noncomputable def kap : Kˣ × Kˣ × Kˣ →* GL (Fin 3) K where
  toFun t := ⟨tm s t.1 t.2.1 t.2.2, tm s (t.1⁻¹ : Kˣ) (t.2.1⁻¹ : Kˣ) (t.2.2⁻¹ : Kˣ),
    tm_mul_inv s _ _ _, tm_inv_mul s _ _ _⟩
  map_one' := by
    apply Units.ext
    simp [tm_one]
  map_mul' a b := by
    apply Units.ext
    simp [tm_mul]

theorem kap_coe (t : Kˣ × Kˣ × Kˣ) :
    ((kap s t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = tm s t.1 t.2.1 t.2.2 := rfl

@[expose] noncomputable def wGL : GL (Fin 3) K := ⟨wm s, wm s, wm_sq s, wm_sq s⟩

theorem wGL_coe : ((wGL s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = wm s := rfl

theorem wGL_conj (t : Kˣ × Kˣ × Kˣ) :
    wGL s * kap s t * (wGL s)⁻¹ = kap s (t.2.1, t.1, t.2.2) := by
  apply Units.ext
  show wm s * tm s t.1 t.2.1 t.2.2 * wm s = tm s t.2.1 t.1 t.2.2
  rw [wm_tm, Matrix.mul_assoc, wm_sq, Matrix.mul_one]

theorem kap_det (t : Kˣ × Kˣ × Kˣ) :
    ((kap s t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = t.1 * t.2.1 * t.2.2 := by
  rw [kap_coe, det_tm]

omit [CharP K 2] in
theorem torus_rel (a : Kˣ) :
    ((a, (1 : Kˣ), a⁻¹) : Kˣ × Kˣ × Kˣ) ^ 2 =
      ((1 : Kˣ), a, a⁻¹) * ((a⁻¹ * a⁻¹, a, a) : Kˣ × Kˣ × Kˣ)⁻¹ := by
  ext <;> simp <;> group

theorem tm_apply_zero_one (x y : K) : tm s x y y 0 1 = x - y := by
  rw [tm_eq_diag]
  simp [e0, fc]

theorem eq_of_tm_scalar (x y c : K) (h : tm s x y y = Matrix.scalar (Fin 3) c) : x = y := by
  have h1 := congrFun (congrFun h 0) 1
  rw [tm_apply_zero_one] at h1
  have h2 : (Matrix.scalar (Fin 3) c : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 := by
    simp [Matrix.scalar_apply]
  rw [h2] at h1
  exact sub_eq_zero.mp h1

theorem torus_elements {M : Type*} [Group M] (ι : M →* GL (Fin 3) K)
    (hι : Function.Injective ι) (a : Kˣ) {n : ℕ} (han : a ^ n = 1) {α δ ω : M}
    (hα : ι α = kap s (1, a, a⁻¹)) (hδ : ι δ = kap s (a⁻¹ * a⁻¹, a, a))
    (hω : ι ω = wGL s) :
    (ω * α * ω⁻¹) ^ 2 = α * δ⁻¹ ∧ α ^ n = 1 ∧ δ ^ n = 1 := by
  refine ⟨hι ?_, hι ?_, hι ?_⟩
  · rw [map_pow, map_mul, map_mul, map_inv, map_mul, map_inv, hα, hδ, hω, wGL_conj, ← map_pow,
      ← map_inv, ← map_mul]
    congr 1
    exact torus_rel a
  · have h1 : ((1, a, a⁻¹) : Kˣ × Kˣ × Kˣ) ^ n = 1 := by
      ext <;> simp [han]
    rw [map_pow, hα, ← map_pow, h1, map_one, map_one]
  · have h1 : ((a⁻¹ * a⁻¹, a, a) : Kˣ × Kˣ × Kˣ) ^ n = 1 := by
      ext <;> simp [han, mul_pow, inv_pow]
    rw [map_pow, hδ, ← map_pow, h1, map_one, map_one]

end CharTwo

end CFSG.CGT.PushingUpLit.CGT6X.End4
