module

public import CFSG.CGT.PushingUpLit.CGT6X.End4Frame
public import CFSG.CGT.PushingUpLit.CGT6X.K7aOrth
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.End4

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.CGT.PushingUpLit.CGT6X.K7a

section Phi

variable {K : Type} [Field K] [CharP K 2] (s : K)

@[expose] def Pfr : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i j => ![fc, fu s, fv s] j i

@[expose] def Qfr : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i j => ![fc, fv s, fu s] i j

theorem Qfr_mul_Pfr : Qfr s * Pfr s = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have h : ∑ k, Qfr s i k * Pfr s k j = ![fc, fv s, fu s] i ⬝ᵥ ![fc, fu s, fv s] j := rfl
  rw [h]
  fin_cases i <;> fin_cases j
  · exact (cc (K := K)).trans (by simp)
  · exact (cu s).trans (by simp)
  · exact (cv s).trans (by simp)
  · exact (vc s).trans (by simp)
  · exact (vu s).trans (by simp)
  · exact (vv s).trans (by simp)
  · exact (uc s).trans (by simp)
  · exact (uu s).trans (by simp)
  · exact (uv s).trans (by simp)

theorem Pfr_mul_Qfr : Pfr s * Qfr s = 1 := mul_eq_one_comm.mp (Qfr_mul_Pfr s)

theorem det_Pfr_mul_det_Qfr : (Pfr s).det * (Qfr s).det = 1 := by
  rw [← det_mul, Pfr_mul_Qfr, det_one]

theorem Pfr_mul_Qfr_mul (M N : Matrix (Fin 3) (Fin 3) K) :
    (Pfr s * M * Qfr s) * (Pfr s * N * Qfr s) = Pfr s * (M * N) * Qfr s := by
  calc (Pfr s * M * Qfr s) * (Pfr s * N * Qfr s)
      = Pfr s * M * (Qfr s * Pfr s) * N * Qfr s := by simp only [Matrix.mul_assoc]
    _ = Pfr s * (M * N) * Qfr s := by rw [Qfr_mul_Pfr, Matrix.mul_one, ← Matrix.mul_assoc]

omit [CharP K 2] in
theorem Pfr_mul_diag_mul (x y z : K) :
    Pfr s * !![x, 0, 0; 0, y, 0; 0, 0, z] * Qfr s = tm s x y z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pfr, Qfr, tm, e0, e1, e2, fc, fu, fv, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

@[expose] def phiFr : SpecialLinearGroup (Fin 3) K →* SpecialLinearGroup (Fin 3) K where
  toFun g := ⟨Pfr s * (g : Matrix (Fin 3) (Fin 3) K) * Qfr s, by
    rw [det_mul, det_mul, g.2, mul_one, det_Pfr_mul_det_Qfr]⟩
  map_one' := by
    apply Subtype.ext
    simp [Pfr_mul_Qfr]
  map_mul' g h := by
    apply Subtype.ext
    simp only [SpecialLinearGroup.coe_mul]
    exact (Pfr_mul_Qfr_mul s _ _).symm

theorem phiFr_coe (g : SpecialLinearGroup (Fin 3) K) :
    ((phiFr s g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Pfr s * (g : Matrix (Fin 3) (Fin 3) K) * Qfr s := rfl

theorem phiFr_injective : Function.Injective (phiFr s) := by
  intro g h hgh
  apply Subtype.ext
  have h1 := congrArg (fun x : SpecialLinearGroup (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hgh
  simp only [phiFr_coe] at h1
  have h2 : Qfr s * (Pfr s * (g : Matrix (Fin 3) (Fin 3) K) * Qfr s) * Pfr s =
      Qfr s * (Pfr s * (h : Matrix (Fin 3) (Fin 3) K) * Qfr s) * Pfr s := by rw [h1]
  have h3 : ∀ m : Matrix (Fin 3) (Fin 3) K,
      Qfr s * (Pfr s * m * Qfr s) * Pfr s = m := fun m => by
    calc Qfr s * (Pfr s * m * Qfr s) * Pfr s = (Qfr s * Pfr s) * m * (Qfr s * Pfr s) := by
          simp only [Matrix.mul_assoc]
      _ = m := by rw [Qfr_mul_Pfr, Matrix.one_mul, Matrix.mul_one]
  rwa [h3, h3] at h2

theorem phiFr_scalar {c : Kˣ} (hc : c ^ 3 = 1) :
    phiFr s (scalarElement c hc) = scalarElement c hc := by
  apply Subtype.ext
  rw [phiFr_coe, coe_scalarElement]
  have : (scalar (Fin 3) (c : K) : Matrix (Fin 3) (Fin 3) K) = (c : K) • 1 := by
    rw [scalar_apply, ← smul_one_eq_diagonal]
  rw [this, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Pfr_mul_Qfr]

end Phi

section Heis

variable {K : Type} [Field K] (ω : K)

@[expose] def l34D : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2]

@[expose] def l34Di : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, ω ^ 2, 0; 0, 0, ω]

@[expose] def l34O : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

@[expose] def l34Oi : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

@[expose] def l34F : Matrix (Fin 3) (Fin 3) K := !![1, 1, 1; 1, ω, ω ^ 2; 1, ω ^ 2, ω]

@[expose] def l34P : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, 1, 0; 0, 0, ω]

@[expose] def l34Pi : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, 1, 0; 0, 0, ω ^ 2]

@[expose] def l34F1 : Matrix (Fin 3) (Fin 3) K := l34P ω * l34F ω * l34Pi ω

@[expose] def l34F2 : Matrix (Fin 3) (Fin 3) K := l34Pi ω * l34F ω * l34P ω

variable {ω} (hω3 : ω ^ 3 = 1)

macro "wclose" : tactic =>
  `(tactic| first | rfl | linear_combination hω3 | linear_combination ω * hω3 |
     linear_combination ω ^ 2 * hω3 | linear_combination (-1 : K) * hω3 |
     linear_combination (-ω) * hω3 | linear_combination (-ω ^ 2) * hω3 |
     linear_combination ω ^ 3 * hω3 | linear_combination (ω ^ 3 + 1) * hω3 |
     (left; linear_combination ω * hω3) | (left; linear_combination (-ω) * hω3) | ring)

include hω3 in
theorem l34_I1 : l34F ω * l34D ω = l34Oi * l34F ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [l34F, l34D, l34Oi, Matrix.mul_apply, Fin.sum_univ_three] <;> wclose

include hω3 in
theorem l34_I2 : l34F1 ω * l34D ω = (l34Di ω * l34Oi) * l34F1 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [l34F1, l34P, l34Pi, l34F, l34D, l34Di, l34Oi, Matrix.mul_apply, Fin.sum_univ_three] <;>
    wclose

include hω3 in
theorem l34_I3 : l34F2 ω * l34D ω = (l34D ω * l34Oi) * l34F2 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [l34F2, l34P, l34Pi, l34F, l34D, l34Oi, Matrix.mul_apply, Fin.sum_univ_three] <;>
    wclose

include hω3 in
theorem l34_I4 : l34O * l34D ω = (ω ^ 2) • (l34D ω * l34O) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l34O, l34D, Matrix.mul_apply, Fin.sum_univ_three] <;> wclose

include hω3 in
theorem l34_cubeD : l34D ω * l34D ω * l34D ω = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l34D, Matrix.mul_apply, Fin.sum_univ_three] <;> wclose

theorem l34_cubeO : l34O * l34O * l34O = (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l34O, Matrix.mul_apply, Fin.sum_univ_three]

include hω3 in
theorem l34_DDi : l34D ω * l34Di ω = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l34D, l34Di, Matrix.mul_apply, Fin.sum_univ_three] <;>
    wclose

theorem l34_OOi : l34O * l34Oi = (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l34O, l34Oi, Matrix.mul_apply, Fin.sum_univ_three]

include hω3 in
theorem l34_det_D : (l34D ω).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [l34D]
  linear_combination hω3

include hω3 in
theorem l34_det_Di : (l34Di ω).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [l34Di]
  linear_combination hω3

theorem l34_det_O : (l34O : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [l34O]

theorem l34_det_Oi : (l34Oi : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [l34Oi]

omit hω3 in
theorem l34_det_P : (l34P ω).det = ω := by
  rw [Matrix.det_fin_three]
  simp [l34P]

omit hω3 in
theorem l34_det_Pi : (l34Pi ω).det = ω ^ 2 := by
  rw [Matrix.det_fin_three]
  simp [l34Pi]

theorem l34_det_F [CharP K 2] (hω : ω ^ 2 + ω + 1 = 0) : (l34F ω).det = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [Matrix.det_fin_three]
  simp [l34F]
  linear_combination (-ω ^ 2 + ω + 3) * hω + (-3 * ω - 2) * h2

theorem l34_det_F1 [CharP K 2] (hω : ω ^ 2 + ω + 1 = 0) (hω3 : ω ^ 3 = 1) :
    (l34F1 ω).det = 1 := by
  rw [l34F1, det_mul, det_mul, l34_det_P, l34_det_Pi, l34_det_F hω]
  linear_combination hω3

theorem l34_det_F2 [CharP K 2] (hω : ω ^ 2 + ω + 1 = 0) (hω3 : ω ^ 3 = 1) :
    (l34F2 ω).det = 1 := by
  rw [l34F2, det_mul, det_mul, l34_det_P, l34_det_Pi, l34_det_F hω]
  linear_combination hω3

end Heis

section SLRel

variable {K : Type} [Field K] [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0)

omit [CharP K 2] in
include hω in
theorem l34_ω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω

omit [CharP K 2] in
include hω in
theorem l34_ω2_cube : (ω ^ 2) ^ 3 = 1 := by
  have h := l34_ω3 hω
  calc (ω ^ 2) ^ 3 = (ω ^ 3) ^ 2 := by ring
    _ = 1 := by rw [h, one_pow]

omit [CharP K 2] in
include hω in
theorem l34_ω_ne_zero : ω ≠ 0 := by
  intro h
  have := l34_ω3 hω
  rw [h] at this
  norm_num at this

include hω in
theorem l34_ω_ne_one : ω ≠ 1 := by
  intro h
  rw [h] at hω
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have : (1 : K) = 0 := by linear_combination hω - h2
  exact one_ne_zero this

@[expose] def l34dSL : SpecialLinearGroup (Fin 3) K := ⟨l34D ω, l34_det_D (l34_ω3 hω)⟩

@[expose] def l34diSL : SpecialLinearGroup (Fin 3) K := ⟨l34Di ω, l34_det_Di (l34_ω3 hω)⟩

@[expose] def l34omSL : SpecialLinearGroup (Fin 3) K := ⟨l34O, l34_det_O⟩

@[expose] def l34oiSL : SpecialLinearGroup (Fin 3) K := ⟨l34Oi, l34_det_Oi⟩

@[expose] def l34fSL : SpecialLinearGroup (Fin 3) K := ⟨l34F ω, l34_det_F hω⟩

@[expose] def l34f1SL : SpecialLinearGroup (Fin 3) K := ⟨l34F1 ω, l34_det_F1 hω (l34_ω3 hω)⟩

@[expose] def l34f2SL : SpecialLinearGroup (Fin 3) K := ⟨l34F2 ω, l34_det_F2 hω (l34_ω3 hω)⟩

@[expose] noncomputable def l34zSL : SpecialLinearGroup (Fin 3) K :=
  scalarElement (Units.mk0 (ω ^ 2) (pow_ne_zero 2 (l34_ω_ne_zero hω)))
    (Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
                   exact l34_ω2_cube hω))

omit [CharP K 2] in
theorem l34_oi : (l34oiSL : SpecialLinearGroup (Fin 3) K) = (l34omSL)⁻¹ := by
  have h : (l34omSL : SpecialLinearGroup (Fin 3) K) * l34oiSL = 1 := Subtype.ext l34_OOi
  exact (inv_eq_of_mul_eq_one_right h).symm

omit [CharP K 2] in
theorem l34_di : l34diSL hω = (l34dSL hω)⁻¹ := by
  have h : l34dSL hω * l34diSL hω = 1 := Subtype.ext (l34_DDi (l34_ω3 hω))
  exact (inv_eq_of_mul_eq_one_right h).symm

omit [CharP K 2] in
theorem l34_d3 : l34dSL hω ^ 3 = 1 := by
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_pow, pow_three']
  exact l34_cubeD (l34_ω3 hω)

omit [CharP K 2] in
theorem l34_o3 : (l34omSL : SpecialLinearGroup (Fin 3) K) ^ 3 = 1 := by
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_pow, pow_three']
  exact l34_cubeO

theorem l34_rel_a : l34fSL hω * l34dSL hω = l34oiSL * l34fSL hω :=
  Subtype.ext (l34_I1 (l34_ω3 hω))

theorem l34_rel_b : l34f1SL hω * l34dSL hω = (l34diSL hω * l34oiSL) * l34f1SL hω :=
  Subtype.ext (l34_I2 (l34_ω3 hω))

theorem l34_rel_c : l34f2SL hω * l34dSL hω = (l34dSL hω * l34oiSL) * l34f2SL hω :=
  Subtype.ext (l34_I3 (l34_ω3 hω))

omit [CharP K 2] in
theorem l34_rel_d : l34omSL * l34dSL hω = l34zSL hω * (l34dSL hω * l34omSL) := by
  apply Subtype.ext
  show l34O * l34D ω = (scalar (Fin 3) (ω ^ 2)) * (l34D ω * l34O)
  rw [l34_I4 (l34_ω3 hω), Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]

omit [CharP K 2] in
theorem l34_z_mem : l34zSL hω ∈ scalars 3 K := scalarElement_mem_scalars _ _

theorem l34_phi_d_mem_orth : phiFr (0 : K) (l34dSL hω) ∈ orthSL K := by
  rw [mem_orthSL, phiFr_coe]
  have h1 := Pfr_mul_diag_mul (K := K) 0 1 ω (ω ^ 2)
  have h2 : ((l34dSL hω : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2] := rfl
  rw [h2, h1, tm_transpose, tm_mul]
  have e1 : ω * ω ^ 2 = 1 := by linear_combination l34_ω3 hω
  have e2 : ω ^ 2 * ω = 1 := by linear_combination l34_ω3 hω
  rw [e1, e2, mul_one]
  exact tm_one 0

theorem l34_phi_d_not_scalar : phiFr (0 : K) (l34dSL hω) ∉ scalars 3 K := by
  rintro ⟨c, hc3, hc⟩
  have hs : phiFr (0 : K) (l34dSL hω) = phiFr (0 : K) (scalarElement c hc3) := by
    rw [phiFr_scalar]
    exact Subtype.ext hc
  have h1 := phiFr_injective (0 : K) hs
  have h11 := congrArg (fun g : SpecialLinearGroup (Fin 3) K =>
    (g : Matrix (Fin 3) (Fin 3) K) 1 1) h1
  have h00 := congrArg (fun g : SpecialLinearGroup (Fin 3) K =>
    (g : Matrix (Fin 3) (Fin 3) K) 0 0) h1
  simp [l34dSL, l34D, scalarElement] at h11 h00
  exact l34_ω_ne_one hω (h11.trans h00.symm)

end SLRel

end CFSG.CGT.PushingUpLit.CGT6X.End4
