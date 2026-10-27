module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerU7Sym
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA7Proj

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KU7

open Matrix Finset CFSG.Open CFSG.LocalAnalysis.ComponentInitial

open scoped Classical

variable {p f : ℕ} {K : Type} [Field K]

abbrev matU {P : Subgroup (GL (Fin 7) K)} (x : P) : Matrix (Fin 7) (Fin 7) K :=
  ((x : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)

theorem matU_mul {P : Subgroup (GL (Fin 7) K)} (x y : P) : matU (x * y) = matU x * matU y := by
  unfold matU
  rw [Subgroup.coe_mul, Units.val_mul]

@[expose] noncomputable def dag (h : UnitaryFieldData p f K) (M : Matrix (Fin 7) (Fin 7) K) :
    Matrix (Fin 7) (Fin 7) K :=
  (M.map h.bar)ᵀ

theorem dag_sum (h : UnitaryFieldData p f K) {ι : Type} (s : Finset ι)
    (M : ι → Matrix (Fin 7) (Fin 7) K) :
    dag h (∑ i ∈ s, M i) = ∑ i ∈ s, dag h (M i) := by
  ext i j
  simp [dag, Matrix.sum_apply, map_sum]

theorem dag_smul (h : UnitaryFieldData p f K) (c : K) (M : Matrix (Fin 7) (Fin 7) K) :
    dag h (c • M) = h.bar c • dag h M := by
  ext i j
  simp [dag, Matrix.smul_apply, map_mul]

@[expose] noncomputable def projU {P : Subgroup (GL (Fin 7) K)} (T : Finset P) :
    Matrix (Fin 7) (Fin 7) K :=
  ((T.card : K))⁻¹ • ∑ x ∈ T, matU x

section Kernel

variable {P : Subgroup (GL (Fin 7) K)} [Fintype P]

theorem projU_left (c : P → K) (hcmul : ∀ x y, c (x * y) = c x * c y)
    (hcpow : ∀ x, c x ^ 3 = 1) {f : P} (hf : c f = 1) :
    matU f * projU (univ.filter fun x => c x = 1) = projU (univ.filter fun x => c x = 1) := by
  unfold projU
  rw [Matrix.mul_smul, Finset.mul_sum]
  congr 1
  have h := KA7.sum_ker_mul hcmul hcpow (fun y : P => matU y) f hf
  simp only [← matU_mul]
  exact h

theorem projU_right (c : P → K) (hcmul : ∀ x y, c (x * y) = c x * c y)
    (hcpow : ∀ x, c x ^ 3 = 1) {f : P} (hf : c f = 1) :
    projU (univ.filter fun x => c x = 1) * matU f = projU (univ.filter fun x => c x = 1) := by
  have hc1 : c 1 = 1 := KA7.char_one hcmul hcpow
  have hfinv : c f⁻¹ = 1 := by
    have h := hcmul f⁻¹ f
    rw [inv_mul_cancel, hc1, hf, mul_one] at h
    exact h.symm
  unfold projU
  rw [Matrix.smul_mul, Finset.sum_mul]
  congr 1
  apply Finset.sum_nbij' (fun x => x * f) (fun x => x * f⁻¹)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hcmul, hx, hf, mul_one]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hcmul, hx, hfinv, mul_one]
  · intro x _
    exact mul_inv_cancel_right x f
  · intro x _
    exact inv_mul_cancel_right x f
  · intro x _
    rw [matU_mul]

theorem projU_mul_self (c : P → K) (hcmul : ∀ x y, c (x * y) = c x * c y)
    (hcpow : ∀ x, c x ^ 3 = 1) (h9 : ((univ.filter fun x => c x = 1).card : K) ≠ 0) :
    projU (univ.filter fun x => c x = 1) * projU (univ.filter fun x => c x = 1) =
      projU (univ.filter fun x => c x = 1) := by
  set T := univ.filter fun x => c x = 1 with hT
  have hS : (∑ x ∈ T, matU x) * (∑ x ∈ T, matU x) = (T.card : K) • ∑ x ∈ T, matU x := by
    rw [Finset.sum_mul]
    have hinner : ∀ x ∈ T, matU x * (∑ y ∈ T, matU y) = ∑ z ∈ T, matU z := by
      intro x hx
      have hcx : c x = 1 := (Finset.mem_filter.mp hx).2
      rw [Finset.mul_sum]
      simp only [← matU_mul]
      exact KA7.sum_ker_mul hcmul hcpow (fun y : P => matU y) x hcx
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, Nat.cast_smul_eq_nsmul]
  unfold projU
  rw [Matrix.smul_mul, Matrix.mul_smul, hS, smul_smul, smul_smul]
  congr 1
  rw [mul_assoc, inv_mul_cancel₀ h9, mul_one]

theorem dag_matU (h : UnitaryFieldData p f K) {P : Subgroup (GL (Fin 7) K)}
    (hP : ∀ x ∈ P, x ∈ StatedSU 7 (p ^ f) K) (x : P) : dag h (matU x) = matU x⁻¹ := by
  have hx := (mem_statedSU_iff h 7 _).mp (hP x x.2)
  obtain ⟨-, hunit⟩ := hx
  have hinv : ((matU x : Matrix (Fin 7) (Fin 7) K))⁻¹ =
      ((matU x : Matrix (Fin 7) (Fin 7) K).map h.bar)ᵀ := Matrix.inv_eq_left_inv hunit
  unfold dag
  rw [← hinv]
  unfold matU
  rw [Subgroup.coe_inv, Matrix.coe_units_inv]

theorem projU_dag (h : UnitaryFieldData p f K)
    (hP : ∀ x ∈ P, x ∈ StatedSU 7 (p ^ f) K) (c : P → K) (hcmul : ∀ x y, c (x * y) = c x * c y)
    (hcinv : ∀ x, c x⁻¹ = (c x)⁻¹) :
    dag h (projU (univ.filter fun x => c x = 1)) = projU (univ.filter fun x => c x = 1) := by
  unfold projU
  rw [dag_smul, dag_sum]
  have hbar : h.bar ((((univ.filter fun x => c x = 1).card : ℕ) : K))⁻¹ =
      (((univ.filter fun x => c x = 1).card : ℕ) : K)⁻¹ := by
    rw [map_inv₀, map_natCast]
  rw [hbar]
  congr 1
  simp only [dag_matU h hP]
  apply Finset.sum_nbij' (fun x : P => x⁻¹) (fun x : P => x⁻¹)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hcinv, hx, inv_one]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hcinv, hx, inv_one]
  · intro x _
    exact inv_inv x
  · intro x _
    exact inv_inv x
  · intro x _
    rfl

theorem conj_mul_eq (A : GL (Fin 7) K) (M N : Matrix (Fin 7) (Fin 7) K) :
    (A : Matrix (Fin 7) (Fin 7) K) * (M * N) * ((A : Matrix (Fin 7) (Fin 7) K))⁻¹ =
      ((A : Matrix (Fin 7) (Fin 7) K) * M * ((A : Matrix (Fin 7) (Fin 7) K))⁻¹) *
        ((A : Matrix (Fin 7) (Fin 7) K) * N * ((A : Matrix (Fin 7) (Fin 7) K))⁻¹) := by
  have hAdet : IsUnit (A : Matrix (Fin 7) (Fin 7) K).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp A.isUnit
  have hinv : ((A : Matrix (Fin 7) (Fin 7) K))⁻¹ * (A : Matrix (Fin 7) (Fin 7) K) = 1 :=
    Matrix.nonsing_inv_mul _ hAdet
  have hexp : ((A : Matrix (Fin 7) (Fin 7) K) * M * ((A : Matrix (Fin 7) (Fin 7) K))⁻¹) *
      ((A : Matrix (Fin 7) (Fin 7) K) * N * ((A : Matrix (Fin 7) (Fin 7) K))⁻¹) =
      (A : Matrix (Fin 7) (Fin 7) K) * M * (((A : Matrix (Fin 7) (Fin 7) K))⁻¹ *
        (A : Matrix (Fin 7) (Fin 7) K)) * N * ((A : Matrix (Fin 7) (Fin 7) K))⁻¹ := by
    simp only [Matrix.mul_assoc]
  rw [hexp, hinv, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem rank_projU (A : GL (Fin 7) K)
    (hA : ∀ x : P, ∀ i j, i ≠ j →
      ((A : Matrix (Fin 7) (Fin 7) K) * matU x * ((A : Matrix (Fin 7) (Fin 7) K))⁻¹) i j = 0)
    (c : P → K) (hcmul : ∀ x y, c (x * y) = c x * c y) (hcpow : ∀ x, c x ^ 3 = 1)
    (hcard : (univ.filter fun x => c x = 1).card = 9) (hk0 : ((9 : ℕ) : K) ≠ 0) :
    (projU (univ.filter fun x => c x = 1)).rank =
      (univ.filter fun i => ∀ x : P, c x = 1 →
        ((A : Matrix (Fin 7) (Fin 7) K) * matU x * ((A : Matrix (Fin 7) (Fin 7) K))⁻¹) i i = 1).card := by
  set T := univ.filter fun x : P => c x = 1 with hT
  have hAdet : IsUnit (A : Matrix (Fin 7) (Fin 7) K).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp A.isUnit
  have hAA : (A : Matrix (Fin 7) (Fin 7) K) * ((A : Matrix (Fin 7) (Fin 7) K))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hAdet
  have hcT : (T.card : K) ≠ 0 := by
    rw [hT, hcard]
    exact hk0
  have hconj : (A : Matrix (Fin 7) (Fin 7) K) * projU T *
      ((A : Matrix (Fin 7) (Fin 7) K))⁻¹ =
      Matrix.diagonal (fun i => ((T.card : K))⁻¹ *
        ∑ x ∈ T, ((A : Matrix (Fin 7) (Fin 7) K) * matU x *
          ((A : Matrix (Fin 7) (Fin 7) K))⁻¹) i i) := by
    unfold projU
    ext i j
    simp only [Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul,
      Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij]
      apply Finset.sum_eq_zero
      intro x _
      rw [hA x i j hij, mul_zero]
  rw [← KA7.rank_conj (A : Matrix (Fin 7) (Fin 7) K) _ _ hAA, hconj, Matrix.rank_diagonal,
    Fintype.card_subtype]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i _
  have hdmul : ∀ x y : P, (fun x : P => ((A : Matrix (Fin 7) (Fin 7) K) * matU x *
      ((A : Matrix (Fin 7) (Fin 7) K))⁻¹) i i) (x * y) =
      (fun x : P => ((A : Matrix (Fin 7) (Fin 7) K) * matU x *
        ((A : Matrix (Fin 7) (Fin 7) K))⁻¹) i i) x *
      (fun x : P => ((A : Matrix (Fin 7) (Fin 7) K) * matU x *
        ((A : Matrix (Fin 7) (Fin 7) K))⁻¹) i i) y := by
    intro x y
    simp only
    rw [matU_mul, conj_mul_eq]
    exact KA7.diag_mul_apply (hA x) (hA y) i
  have hsum := KA7.sum_ker_char (d := fun x : P => ((A : Matrix (Fin 7) (Fin 7) K) * matU x *
      ((A : Matrix (Fin 7) (Fin 7) K))⁻¹) i i) hcmul hcpow hdmul
  rw [← hT] at hsum
  rw [hsum]
  split_ifs with htriv
  · rw [inv_mul_cancel₀ hcT]
    exact ⟨fun _ => htriv, fun _ => one_ne_zero⟩
  · rw [mul_zero]
    exact ⟨fun h => absurd rfl h, fun h => absurd h htriv⟩

end Kernel

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KU7

end
