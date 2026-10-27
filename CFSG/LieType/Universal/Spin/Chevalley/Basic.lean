module

public import CFSG.LieType.Universal.Spin.RootElements

public section

namespace CFSG.LieType.Universal.Spin

open CliffordAlgebra QuadraticMap

variable {K : Type*} [Field K]

section Vectors

variable {V : Type*} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)

theorem ι_mul_ι_eq_neg_of_polar_eq_zero {a b : V} (h : polar Q a b = 0) :
    ι Q a * ι Q b = -(ι Q b * ι Q a) := by
  rw [ι_mul_ι_comm, h, map_zero, zero_sub]

theorem ι_mul_ι_self_eq_zero {a : V} (h : Q a = 0) : ι Q a * ι Q a = 0 := by
  rw [ι_sq_scalar, h, map_zero]

theorem ι_mul_ι_mul_eq_zero {a : V} (h : Q a = 0) (x : CliffordAlgebra Q) :
    ι Q a * (ι Q a * x) = 0 := by
  rw [← mul_assoc, ι_mul_ι_self_eq_zero Q h, zero_mul]

theorem ι_mul_ι_add_ι_mul_ι_eq_one {a b : V} (h : polar Q a b = 1) :
    ι Q a * ι Q b + ι Q b * ι Q a = 1 := by
  rw [ι_mul_ι_add_swap, h, map_one]

theorem ι_mul_ι_mul_ι_eq_self {a b : V} (ha : Q a = 0) (h : polar Q a b = 1) :
    ι Q a * (ι Q b * ι Q a) = ι Q a := by
  rw [← mul_assoc, ι_mul_ι_mul_ι, h, ha, one_smul, zero_smul, sub_zero]

theorem ι_mul_ι_mul_ι_comm {a b v : V} (ha : polar Q v a = 0) (hb : polar Q v b = 0) :
    ι Q v * (ι Q a * ι Q b) = ι Q a * ι Q b * ι Q v := by
  rw [← mul_assoc, ι_mul_ι_eq_neg_of_polar_eq_zero Q ha, neg_mul, mul_assoc,
    ι_mul_ι_eq_neg_of_polar_eq_zero Q hb, mul_neg, neg_neg, mul_assoc]

theorem ι_mul_ι_mul_ι_mul_comm {a b v : V} (ha : polar Q v a = 0) (hb : polar Q v b = 0)
    (x : CliffordAlgebra Q) : ι Q v * (ι Q a * (ι Q b * x)) = ι Q a * (ι Q b * (ι Q v * x)) := by
  rw [← mul_assoc (ι Q a), ← mul_assoc, ι_mul_ι_mul_ι_comm Q ha hb, mul_assoc, mul_assoc]

theorem ι_mul_ι_mul_ι_mul_eq {a b : V} (ha : Q a = 0) (h : polar Q a b = 1)
    (x : CliffordAlgebra Q) : ι Q a * (ι Q b * (ι Q a * x)) = ι Q a * x := by
  rw [← mul_assoc (ι Q b), ← mul_assoc, ι_mul_ι_mul_ι_eq_self Q ha h]

theorem ι_mul_ι_mul_eq_of_map_eq_one {z : V} (h : Q z = 1) (x : CliffordAlgebra Q) :
    ι Q z * (ι Q z * x) = x := by
  rw [← mul_assoc, ι_sq_scalar, h, map_one, one_mul]

theorem ι_mul_ι_mul_ι_mul_ι_eq_neg {z x : V} (hz : Q z = 1) (hxz : polar Q x z = 0) (y : V) :
    ι Q z * ι Q x * (ι Q z * ι Q y) = -(ι Q x * ι Q y) := by
  rw [mul_assoc, ← mul_assoc (ι Q x), ι_mul_ι_eq_neg_of_polar_eq_zero Q hxz, neg_mul, mul_neg,
    mul_assoc, ι_mul_ι_mul_eq_of_map_eq_one Q hz]

theorem coe_mul_eq_neg_of_conj {g x : spinGroup Q}
    (h : (g : CliffordAlgebra Q) * x * ↑g⁻¹ = -(x : CliffordAlgebra Q)) :
    (g : CliffordAlgebra Q) * x = -((x : CliffordAlgebra Q) * g) := by
  calc (g : CliffordAlgebra Q) * x = g * x * ↑g⁻¹ * g := by
        rw [mul_assoc _ (↑g⁻¹ : CliffordAlgebra Q), coe_inv_mul_coe, mul_one]
    _ = -((x : CliffordAlgebra Q) * g) := by rw [h, neg_mul]

theorem ι_mul_ι_mul_ι_mul_ι_mul_ι_mul_ι {a b a' b' : V} (ha : Q a = 0) (hb : Q b = 0)
    (haa : polar Q a a' = 1) (hbb : polar Q b b' = 1) (hba : polar Q b a = 0)
    (hba' : polar Q b a' = 0) (hb'a : polar Q b' a = 0) (hb'a' : polar Q b' a' = 0) :
    ι Q a * ι Q b * (ι Q b' * ι Q a' * (ι Q a * ι Q b)) = ι Q a * ι Q b := by
  simp only [mul_assoc]
  rw [ι_mul_ι_mul_ι_mul_comm Q hb'a' hb'a, ι_mul_ι_mul_ι_mul_comm Q hba' hba,
    ι_mul_ι_mul_ι_mul_eq Q ha haa, ι_mul_ι_mul_ι_eq_self Q hb hbb]

theorem commute_ι_mul_ι {a b c d : V} (hac : polar Q a c = 0) (had : polar Q a d = 0)
    (hbc : polar Q b c = 0) (hbd : polar Q b d = 0) :
    Commute (ι Q a * ι Q b) (ι Q c * ι Q d) := by
  change ι Q a * ι Q b * (ι Q c * ι Q d) = ι Q c * ι Q d * (ι Q a * ι Q b)
  rw [mul_assoc, ι_mul_ι_mul_ι_comm Q hbc hbd, ← mul_assoc, ι_mul_ι_mul_ι_comm Q hac had,
    mul_assoc]

theorem coe_mul_ι_mul_ι_mul_coe_inv (g : spinGroup Q) (a b : V) :
    (g : CliffordAlgebra Q) * (ι Q a * ι Q b) * ↑g⁻¹ =
      ι Q (spinAction Q g a) * ι Q (spinAction Q g b) := by
  rw [ι_spinAction, ι_spinAction]
  simp only [mul_assoc, coe_inv_mul_coe_mul]

theorem coe_mul_one_add_smul_mul_coe_inv (g : spinGroup Q) (a b : V) (c : K) :
    (g : CliffordAlgebra Q) * (1 + c • (ι Q a * ι Q b)) * ↑g⁻¹ =
      1 + c • (ι Q (spinAction Q g a) * ι Q (spinAction Q g b)) := by
  rw [← coe_mul_ι_mul_ι_mul_coe_inv, mul_add, add_mul, mul_one, coe_mul_coe_inv, mul_smul_comm,
    smul_mul_assoc]

theorem conj_rootHom (g : spinGroup Q) {u w : V} (hu : Q u = 0) (huw : polar Q u w = 0)
    (hmem : ∀ c : K, 1 + c • (ι Q w * ι Q u) ∈ spinGroup Q) {u' w' : V} (hu' : Q u' = 0)
    (huw' : polar Q u' w' = 0) (hmem' : ∀ c : K, 1 + c • (ι Q w' * ι Q u') ∈ spinGroup Q)
    (hgu : spinAction Q g u = u') (hgw : spinAction Q g w = w') (c : Multiplicative K) :
    g * rootHom Q hu huw hmem c * g⁻¹ = rootHom Q hu' huw' hmem' c := by
  apply Subtype.ext
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← ofAdd_toAdd c, coe_rootHom, coe_rootHom,
    coe_mul_one_add_smul_mul_coe_inv, hgu, hgw]

end Vectors

section Matrices

open Matrix

@[expose] noncomputable def upperSL2 (c : K) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, c; 0, 1], by simp [det_fin_two]⟩

@[expose] noncomputable def lowerSL2 (c : K) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 0; c, 1], by simp [det_fin_two]⟩

@[expose] noncomputable def weylSL2 (t : Kˣ) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, (t : K); -(t⁻¹ : Kˣ), 0], by simp [det_fin_two]⟩

@[expose] noncomputable def diagSL2 : Kˣ →* SpecialLinearGroup (Fin 2) K where
  toFun t := ⟨!![(t : K), 0; 0, (t⁻¹ : Kˣ)], by simp [det_fin_two]⟩
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' s t := by
    apply Subtype.ext
    change _ = (⟨!![(s : K), 0; 0, (s⁻¹ : Kˣ)], _⟩ : SpecialLinearGroup (Fin 2) K).1 *
      (⟨!![(t : K), 0; 0, (t⁻¹ : Kˣ)], _⟩ : SpecialLinearGroup (Fin 2) K).1
    simp [mul_comm]

@[simp]
theorem coe_upperSL2 (c : K) : (upperSL2 c : Matrix (Fin 2) (Fin 2) K) = !![1, c; 0, 1] := rfl

@[simp]
theorem coe_lowerSL2 (c : K) : (lowerSL2 c : Matrix (Fin 2) (Fin 2) K) = !![1, 0; c, 1] := rfl

@[simp]
theorem coe_weylSL2 (t : Kˣ) :
    (weylSL2 t : Matrix (Fin 2) (Fin 2) K) = !![0, (t : K); -(t⁻¹ : Kˣ), 0] := rfl

@[simp]
theorem coe_diagSL2 (t : Kˣ) :
    (diagSL2 t : Matrix (Fin 2) (Fin 2) K) = !![(t : K), 0; 0, (t⁻¹ : Kˣ)] := rfl

theorem upperSL2_add (b c : K) : upperSL2 (b + c) = upperSL2 b * upperSL2 c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two, add_comm]

theorem lowerSL2_add (b c : K) : lowerSL2 (b + c) = lowerSL2 b * lowerSL2 c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two, add_comm]

@[simp]
theorem upperSL2_zero : upperSL2 (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[simp]
theorem lowerSL2_zero : lowerSL2 (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem weylSL2_eq (t : Kˣ) :
    weylSL2 t = upperSL2 (t : K) * lowerSL2 (-(t⁻¹ : Kˣ) : K) * upperSL2 (t : K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]

theorem diagSL2_eq (t : Kˣ) : diagSL2 t = weylSL2 t * weylSL2 (-1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]

theorem weylSL2_one_mul_self : weylSL2 (1 : Kˣ) * weylSL2 1 = diagSL2 (-1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]

theorem weylSL2_one_inv : (weylSL2 (1 : Kˣ))⁻¹ = weylSL2 (-1) := by
  rw [inv_eq_iff_mul_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]

theorem weylSL2_mul_diagSL2_mul_inv (t : Kˣ) :
    weylSL2 1 * diagSL2 t * (weylSL2 1)⁻¹ = diagSL2 t⁻¹ := by
  rw [weylSL2_one_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]

theorem weylSL2_one_mul_inv (l : Kˣ) : weylSL2 1 * (weylSL2 l)⁻¹ = diagSL2 l⁻¹ := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]

theorem exists_eq_lowerSL2_mul_upperSL2_mul_lowerSL2_mul_upperSL2
    (M : SpecialLinearGroup (Fin 2) K) :
    ∃ a b c d : K, M = lowerSL2 a * upperSL2 b * lowerSL2 c * upperSL2 d := by
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [← det_fin_two]
    exact M.2
  by_cases h : M 1 0 = 0
  · have h0 : M 0 0 ≠ 0 := by
      intro h0
      rw [h0, h] at hdet
      simp at hdet
    have h11 : M 1 1 = (M 0 0)⁻¹ := by
      rw [h, mul_zero, sub_zero] at hdet
      exact eq_inv_of_mul_eq_one_right hdet
    refine ⟨1, (M 0 0 - 1) / (-M 0 0), -M 0 0, (M 1 1 - M 0 1 - 1) / (-M 0 0), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_two, h, h11] <;> field_simp <;> ring
  · have h01 : M 0 1 = (M 0 0 * M 1 1 - 1) / M 1 0 := by
      field_simp
      linear_combination -hdet
    refine ⟨0, (M 0 0 - 1) / M 1 0, M 1 0, (M 1 1 - 1) / M 1 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_two, h01] <;> field_simp <;> ring

theorem mem_closure_upperSL2_lowerSL2 {G : Type*} [Group G]
    (ρ : SpecialLinearGroup (Fin 2) K →* G) (M : SpecialLinearGroup (Fin 2) K) :
    ρ M ∈ Subgroup.closure (Set.range (fun c : K => ρ (upperSL2 c)) ∪
      Set.range (fun c : K => ρ (lowerSL2 c))) := by
  obtain ⟨a, b, c, d, rfl⟩ := exists_eq_lowerSL2_mul_upperSL2_mul_lowerSL2_mul_upperSL2 M
  simp only [map_mul]
  have hU : ∀ x : K, ρ (upperSL2 x) ∈ Subgroup.closure (Set.range (fun c : K => ρ (upperSL2 c)) ∪
      Set.range (fun c : K => ρ (lowerSL2 c))) := fun x =>
    Subgroup.subset_closure (Or.inl ⟨x, rfl⟩)
  have hL : ∀ x : K, ρ (lowerSL2 x) ∈ Subgroup.closure (Set.range (fun c : K => ρ (upperSL2 c)) ∪
      Set.range (fun c : K => ρ (lowerSL2 c))) := fun x =>
    Subgroup.subset_closure (Or.inr ⟨x, rfl⟩)
  exact mul_mem (mul_mem (mul_mem (hL a) (hU b)) (hL c)) (hU d)

theorem weylSL2_conj_of_conj {G : Type*} [Group G] (ρ : SpecialLinearGroup (Fin 2) K →* G)
    (h : G) (l : Kˣ) (hU : ∀ c : K, h * ρ (upperSL2 c) * h⁻¹ = ρ (upperSL2 ((l : K) * c)))
    (hL : ∀ c : K, h * ρ (lowerSL2 c) * h⁻¹ = ρ (lowerSL2 (((l⁻¹ : Kˣ) : K) * c))) :
    ρ (weylSL2 1) * h * (ρ (weylSL2 1))⁻¹ = ρ (diagSL2 l⁻¹) * h := by
  have hw : h * ρ (weylSL2 1) * h⁻¹ = ρ (weylSL2 l) := by
    have e : ∀ x y z : G, h * (x * y * z) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) * (h * z * h⁻¹) :=
      fun x y z => by group
    rw [weylSL2_eq, map_mul, map_mul, e, hU, hL, weylSL2_eq, map_mul, map_mul]
    simp
  have key : ρ (weylSL2 1) * h * (ρ (weylSL2 1))⁻¹ =
      ρ (weylSL2 1) * (h * ρ (weylSL2 1) * h⁻¹)⁻¹ * h := by group
  rw [key, hw, ← map_inv, ← map_mul, weylSL2_one_mul_inv]

end Matrices

section SL2Pair

variable {A : Type*} [Ring A]

structure SL2Pair (A : Type*) [Ring A] where
  X : A
  Y : A
  X_mul_X : X * X = 0
  Y_mul_Y : Y * Y = 0
  X_mul_Y_mul_X : X * (Y * X) = X
  Y_mul_X_mul_Y : Y * (X * Y) = Y

namespace SL2Pair

variable (P : SL2Pair A)

theorem X_mul_X_mul (a : A) : P.X * (P.X * a) = 0 := by
  rw [← mul_assoc, P.X_mul_X, zero_mul]

theorem Y_mul_Y_mul (a : A) : P.Y * (P.Y * a) = 0 := by
  rw [← mul_assoc, P.Y_mul_Y, zero_mul]

theorem X_mul_Y_mul_X_mul (a : A) : P.X * (P.Y * (P.X * a)) = P.X * a := by
  rw [← mul_assoc P.Y, ← mul_assoc, P.X_mul_Y_mul_X]

theorem Y_mul_X_mul_Y_mul (a : A) : P.Y * (P.X * (P.Y * a)) = P.Y * a := by
  rw [← mul_assoc P.X, ← mul_assoc, P.Y_mul_X_mul_Y]

variable [Algebra K A]

@[expose] noncomputable def toFun (M : Matrix (Fin 2) (Fin 2) K) : A :=
  M 0 0 • (P.X * P.Y) + M 0 1 • P.X + M 1 0 • P.Y + M 1 1 • (P.Y * P.X) +
    (1 - P.X * P.Y - P.Y * P.X)

theorem toFun_mul (M N : Matrix (Fin 2) (Fin 2) K) :
    P.toFun (M * N) = P.toFun M * P.toFun N := by
  simp only [toFun, Matrix.mul_apply, Fin.sum_univ_two, add_mul, mul_add, sub_mul, mul_sub,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one, mul_assoc, P.X_mul_X, P.Y_mul_Y,
    P.X_mul_X_mul, P.Y_mul_Y_mul, P.X_mul_Y_mul_X, P.Y_mul_X_mul_Y, smul_zero, mul_zero]
  module

theorem toFun_one : P.toFun (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  simp only [toFun, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), one_smul, zero_smul, add_zero]
  abel

@[expose] noncomputable def toMatrixHom : Matrix (Fin 2) (Fin 2) K →* A where
  toFun := P.toFun
  map_one' := P.toFun_one
  map_mul' := P.toFun_mul

theorem toMatrixHom_apply (M : Matrix (Fin 2) (Fin 2) K) : P.toMatrixHom M = P.toFun M := rfl

@[simp]
theorem toFun_upperSL2 (c : K) :
    P.toFun ((upperSL2 c : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      1 + c • P.X := by
  simp only [toFun, coe_upperSL2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, one_smul, zero_smul,
    add_zero]
  abel

@[simp]
theorem toFun_lowerSL2 (c : K) :
    P.toFun ((lowerSL2 c : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      1 + c • P.Y := by
  simp only [toFun, coe_lowerSL2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, one_smul, zero_smul,
    add_zero]
  abel

theorem toFun_weylSL2 (t : Kˣ) :
    P.toFun ((weylSL2 t : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (t : K) • P.X - ((t⁻¹ : Kˣ) : K) • P.Y + (1 - P.X * P.Y - P.Y * P.X) := by
  simp only [toFun, coe_weylSL2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, zero_smul, zero_add,
    add_zero, neg_smul, sub_eq_add_neg]

theorem toFun_diagSL2 (t : Kˣ) :
    P.toFun ((diagSL2 t : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (t : K) • (P.X * P.Y) + ((t⁻¹ : Kˣ) : K) • (P.Y * P.X) + (1 - P.X * P.Y - P.Y * P.X) := by
  simp only [toFun, coe_diagSL2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, zero_smul, add_zero]

theorem map_toFun {B : Type*} [Ring B] [Algebra K B] (f : A →ₐ[K] B) (P' : SL2Pair B)
    (hX : f P.X = P'.X) (hY : f P.Y = P'.Y) (M : Matrix (Fin 2) (Fin 2) K) :
    f (P.toFun M) = P'.toFun M := by
  simp only [toFun, map_add, map_sub, map_smul, map_mul, map_one, hX, hY]

theorem commute_toFun_diagSL2 {y : A} (h₁ : Commute (P.X * P.Y) y) (h₂ : Commute (P.Y * P.X) y)
    (t : Kˣ) :
    Commute (P.toFun ((diagSL2 t : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K)) y := by
  rw [toFun_diagSL2]
  exact ((h₁.smul_left _).add_left (h₂.smul_left _)).add_left
    (((Commute.one_left y).sub_left h₁).sub_left h₂)

theorem toFun_mem (S : Submonoid A) (hX : ∀ c : K, 1 + c • P.X ∈ S)
    (hY : ∀ c : K, 1 + c • P.Y ∈ S) (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    P.toFun (M : Matrix (Fin 2) (Fin 2) K) ∈ S := by
  obtain ⟨a, b, c, d, rfl⟩ := exists_eq_lowerSL2_mul_upperSL2_mul_lowerSL2_mul_upperSL2 M
  simp only [Matrix.SpecialLinearGroup.coe_mul, ← P.toMatrixHom_apply, map_mul]
  simp only [P.toMatrixHom_apply, toFun_upperSL2, toFun_lowerSL2]
  exact mul_mem (mul_mem (mul_mem (hY a) (hX b)) (hY c)) (hX d)

variable {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] noncomputable def toSpin (P : SL2Pair (CliffordAlgebra Q))
    (hX : ∀ c : K, 1 + c • P.X ∈ spinGroup Q) (hY : ∀ c : K, 1 + c • P.Y ∈ spinGroup Q) :
    Matrix.SpecialLinearGroup (Fin 2) K →* spinGroup Q :=
  (P.toMatrixHom.comp Matrix.SpecialLinearGroup.coeMonoidHom).codRestrict (spinGroup Q)
    (P.toFun_mem (spinGroup Q) hX hY)

theorem coe_toSpin (P : SL2Pair (CliffordAlgebra Q))
    (hX : ∀ c : K, 1 + c • P.X ∈ spinGroup Q) (hY : ∀ c : K, 1 + c • P.Y ∈ spinGroup Q)
    (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    (P.toSpin hX hY M : CliffordAlgebra Q) = P.toFun (M : Matrix (Fin 2) (Fin 2) K) := rfl

end SL2Pair

end SL2Pair

end CFSG.LieType.Universal.Spin
