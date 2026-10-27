module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320Gen

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320

open Matrix Matrix.SpecialLinearGroup CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine

variable {k : Type} [Field k] [CharP k 2] {ω : k} (hω : ω * ω + ω + 1 = 0)

@[expose] def Mm (ω : k) : Matrix (Fin 3) (Fin 3) k := !![0, 0, ω; 1, 0, 0; 0, 1, 0]

def tauM0 (ω : k) : Matrix (Fin 3) (Fin 3) k := !![0, 1, ω; 1, 0, 1; ω*ω, 1, 0]

def tauM1 (ω : k) : Matrix (Fin 3) (Fin 3) k := !![0, ω*ω, 1; ω, 0, 1; 1, 1, 0]

def tauM2 (ω : k) : Matrix (Fin 3) (Fin 3) k := !![0, 1, 1; 1, 0, ω*ω; 1, ω, 0]

include hω in
theorem tauM0_pow2 : tauM0 ω ^ 2 = !![0, ω, 1; ω*ω, 0, ω; 1, ω*ω, 0] := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tauM0, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

include hω in
theorem tauM0_pow3 : tauM0 ω ^ 3 = !![1, 1, ω; 1, 1, 1; ω*ω, 1, 1] := by
  rw [pow_succ, tauM0_pow2 hω]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tauM0, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

include hω in
theorem tauM0_pow4 : tauM0 ω ^ 4 = !![0, ω*ω, ω*ω; ω, 0, ω*ω; ω, ω, 0] := by
  rw [pow_succ, tauM0_pow3 hω]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tauM0, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

include hω in
theorem tauM0_pow5 : tauM0 ω ^ 5 = !![1, ω*ω, ω*ω; ω, 1, ω*ω; ω, ω, 1] := by
  rw [pow_succ, tauM0_pow4 hω]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tauM0, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

include hω in
theorem tauM0_pow6 : tauM0 ω ^ 6 = !![1, ω, 1; ω*ω, 1, ω; 1, ω*ω, 1] := by
  rw [pow_succ, tauM0_pow5 hω]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tauM0, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

include hω in
theorem tauM0_pow7 : tauM0 ω ^ 7 = !![1, 0, 0; 0, 1, 0; 0, 0, 1] := by
  rw [pow_succ, tauM0_pow6 hω]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tauM0, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

include hω in
theorem tauM1_pow2 : tauM1 ω ^ 2 = !![0, 1, ω*ω; 1, 0, ω; ω, ω*ω, 0] := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tauM1, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

include hω in
theorem tauM1_pow3 : tauM1 ω ^ 3 = !![1, ω*ω, 1; ω, 1, 1; 1, 1, 1] := by
  rw [pow_succ, tauM1_pow2 hω]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tauM1, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

include hω in
theorem tauM1_pow4 : tauM1 ω ^ 4 = !![0, ω, ω; ω*ω, 0, ω*ω; ω*ω, ω, 0] := by
  rw [pow_succ, tauM1_pow3 hω]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tauM1, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

include hω in
theorem tauM1_pow5 : tauM1 ω ^ 5 = !![1, ω, ω; ω*ω, 1, ω*ω; ω*ω, ω, 1] := by
  rw [pow_succ, tauM1_pow4 hω]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tauM1, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

include hω in
theorem tauM1_pow6 : tauM1 ω ^ 6 = !![1, 1, ω*ω; 1, 1, ω; ω, ω*ω, 1] := by
  rw [pow_succ, tauM1_pow5 hω]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tauM1, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

include hω in
theorem tauM2_pow2 : tauM2 ω ^ 2 = !![0, ω, ω*ω; ω*ω, 0, 1; ω, 1, 0] := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tauM2, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

include hω in
theorem tauM2_pow3 : tauM2 ω ^ 3 = !![1, 1, 1; 1, 1, ω*ω; 1, ω, 1] := by
  rw [pow_succ, tauM2_pow2 hω]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tauM2, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

include hω in
theorem tauM2_pow4 : tauM2 ω ^ 4 = !![0, ω*ω, ω; ω, 0, ω; ω*ω, ω*ω, 0] := by
  rw [pow_succ, tauM2_pow3 hω]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tauM2, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

include hω in
theorem tauM2_pow5 : tauM2 ω ^ 5 = !![1, ω*ω, ω; ω, 1, ω; ω*ω, ω*ω, 1] := by
  rw [pow_succ, tauM2_pow4 hω]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tauM2, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

include hω in
theorem tauM2_pow6 : tauM2 ω ^ 6 = !![1, ω, ω*ω; ω*ω, 1, 1; ω, 1, 1] := by
  rw [pow_succ, tauM2_pow5 hω]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tauM2, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

include hω in
theorem det_tauM0 : (tauM0 ω).det = 1 := by
  simp [tauM0, Matrix.det_fin_three]
  grind

@[expose] def tau0 : SpecialLinearGroup (Fin 3) k := ⟨tauM0 ω, det_tauM0 hω⟩

@[expose] def tau1 : SpecialLinearGroup (Fin 3) k := rSL * tau0 hω * rSL⁻¹

@[expose] def tau2 : SpecialLinearGroup (Fin 3) k := rSL * tau1 hω * rSL⁻¹

theorem coe_tau0 : ((tau0 hω : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = tauM0 ω := rfl

theorem coe_tau1 : ((tau1 hω : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = tauM1 ω := by
  rw [tau1, rSL_inv, coe_mul, coe_mul, coe_mul, coe_rSL, coe_tau0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tauM0, tauM1, Matrix.mul_apply, Fin.sum_univ_three]

theorem coe_tau2 : ((tau2 hω : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = tauM2 ω := by
  rw [tau2, rSL_inv, coe_mul, coe_mul, coe_mul, coe_rSL, coe_tau1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tauM1, tauM2, Matrix.mul_apply, Fin.sum_univ_three]

include hω in
theorem tau0_pow_seven : tau0 hω ^ 7 = 1 := by
  apply Subtype.ext
  rw [coe_pow, coe_tau0, tauM0_pow7 hω, coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

include hω in
theorem coe_word1 : (((tau2 hω ^ 6 * tau1 hω ^ 6 * tau0 hω ^ 5 * tau1 hω ^ 4 * tau2 hω ^ 4 : SpecialLinearGroup (Fin 3) k)) : Matrix (Fin 3) (Fin 3) k) = !![ω*ω, ω*ω, 0; 0, ω*ω, 0; 0, 0, ω*ω] := by
  simp only [coe_mul, coe_pow, coe_tau0, coe_tau1, coe_tau2]
  rw [tauM2_pow6 hω, tauM1_pow6 hω, tauM0_pow5 hω, tauM1_pow4 hω, tauM2_pow4 hω]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> grind

include hω in
theorem coe_wordw : (((tau0 hω ^ 5 * tau2 hω ^ 6 * tau1 hω ^ 6 * tau2 hω ^ 4 * tau0 hω : SpecialLinearGroup (Fin 3) k)) : Matrix (Fin 3) (Fin 3) k) = !![ω*ω, 1, 0; 0, ω*ω, 0; 0, 0, ω*ω] := by
  simp only [coe_mul, coe_pow, coe_tau0, coe_tau1, coe_tau2]
  rw [tauM0_pow5 hω, tauM2_pow6 hω, tauM1_pow6 hω, tauM2_pow4 hω]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tauM0, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

include hω in
theorem coe_wordw2 : (((tau1 hω ^ 6 * tau0 hω ^ 5 * tau2 hω ^ 6 * tau0 hω * tau1 hω ^ 4 : SpecialLinearGroup (Fin 3) k)) : Matrix (Fin 3) (Fin 3) k) = !![ω*ω, ω, 0; 0, ω*ω, 0; 0, 0, ω*ω] := by
  simp only [coe_mul, coe_pow, coe_tau0, coe_tau1, coe_tau2]
  rw [tauM1_pow6 hω, tauM0_pow5 hω, tauM2_pow6 hω, tauM1_pow4 hω]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tauM0, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

include hω in
theorem x01_mem_of_tau (hall : ∀ a : k, a = 0 ∨ a = 1 ∨ a = ω ∨ a = ω * ω)
    (H : Subgroup (SpecialLinearGroup (Fin 3) k))
    (h0 : tau0 hω ∈ H) (h1 : tau1 hω ∈ H) (h2 : tau2 hω ∈ H) (c : k) : x01 c ∈ H := by
  set W1 : SpecialLinearGroup (Fin 3) k :=
    tau2 hω ^ 6 * tau1 hω ^ 6 * tau0 hω ^ 5 * tau1 hω ^ 4 * tau2 hω ^ 4 with hW1
  set Ww : SpecialLinearGroup (Fin 3) k :=
    tau0 hω ^ 5 * tau2 hω ^ 6 * tau1 hω ^ 6 * tau2 hω ^ 4 * tau0 hω with hWw
  set Ww2 : SpecialLinearGroup (Fin 3) k :=
    tau1 hω ^ 6 * tau0 hω ^ 5 * tau2 hω ^ 6 * tau0 hω * tau1 hω ^ 4 with hWw2
  have hm1 : W1 ∈ H := mul_mem (mul_mem (mul_mem (mul_mem (pow_mem h2 _) (pow_mem h1 _))
    (pow_mem h0 _)) (pow_mem h1 _)) (pow_mem h2 _)
  have hmw : Ww ∈ H := mul_mem (mul_mem (mul_mem (mul_mem (pow_mem h0 _) (pow_mem h2 _))
    (pow_mem h1 _)) (pow_mem h2 _)) h0
  have hmw2 : Ww2 ∈ H := mul_mem (mul_mem (mul_mem (mul_mem (pow_mem h1 _) (pow_mem h0 _))
    (pow_mem h2 _)) h0) (pow_mem h1 _)
  have c1 : ((W1 : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      !![ω*ω, ω*ω, 0; 0, ω*ω, 0; 0, 0, ω*ω] := coe_word1 hω
  have cw : ((Ww : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      !![ω*ω, 1, 0; 0, ω*ω, 0; 0, 0, ω*ω] := coe_wordw hω
  have cw2 : ((Ww2 : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      !![ω*ω, ω, 0; 0, ω*ω, 0; 0, 0, ω*ω] := coe_wordw2 hω
  have e1 : W1 = Ww * x01 (ω * ω) := by
    apply Subtype.ext
    rw [coe_mul Ww (x01 (ω * ω)), c1, cw, coe_x01]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    all_goals grind
  have e2 : Ww = Ww2 * x01 1 := by
    apply Subtype.ext
    rw [coe_mul Ww2 (x01 1), cw, cw2, coe_x01]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    all_goals grind
  have e3 : Ww2 = W1 * x01 ω := by
    apply Subtype.ext
    rw [coe_mul W1 (x01 ω), c1, cw2, coe_x01]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    all_goals grind
  rcases hall c with h | h | h | h <;> rw [h]
  · have : x01 (0 : k) = 1 := by
      apply Subtype.ext
      rw [coe_x01, coe_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [this]
    exact one_mem H
  · have : x01 (1 : k) = Ww2⁻¹ * Ww := eq_inv_mul_of_mul_eq e2.symm
    rw [this]
    exact mul_mem (inv_mem hmw2) hmw
  · have : x01 ω = W1⁻¹ * Ww2 := eq_inv_mul_of_mul_eq e3.symm
    rw [this]
    exact mul_mem (inv_mem hm1) hmw2
  · have : x01 (ω * ω) = Ww⁻¹ * W1 := eq_inv_mul_of_mul_eq e1.symm
    rw [this]
    exact mul_mem (inv_mem hmw) hm1

include hω in
theorem tauM0_eq : tauM0 ω = Mm ω + (ω * ω) • (Mm ω * Mm ω) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tauM0, Mm] <;> grind

include hω in
theorem Mm_comm_tauM0 : Mm ω * tauM0 ω = tauM0 ω * Mm ω := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tauM0, Mm, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

include hω in
theorem tau_mul_conj {g : Matrix (Fin 3) (Fin 3) k} {c : k} (hc : c = 1 ∨ c = ω ∨ c = ω * ω)
    (h : Mm ω * g = c • (g * Mm ω)) : ∃ e : ℕ, tauM0 ω * g = g * tauM0 ω ^ e := by
  have h2 : Mm ω * (Mm ω * g) = (c * c) • (g * (Mm ω * Mm ω)) := by
    rw [h, Matrix.mul_smul, ← Matrix.mul_assoc, h, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
  have key : tauM0 ω * g = g * (c • Mm ω + (ω * ω * (c * c)) • (Mm ω * Mm ω)) := by
    rw [tauM0_eq hω, Matrix.add_mul, smul_mul_assoc, Matrix.mul_assoc (Mm ω) (Mm ω) g, h2, h,
      Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, smul_smul]
  rcases hc with h1 | h1 | h1
  · refine ⟨1, ?_⟩
    rw [key, pow_one, tauM0_eq hω, h1]
    congr 1
    simp
  · refine ⟨4, ?_⟩
    rw [key, tauM0_pow4 hω, h1]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Mm] <;> grind
  · refine ⟨2, ?_⟩
    rw [key, tauM0_pow2 hω, h1]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Mm] <;> grind

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320
