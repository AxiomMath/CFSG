module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA6UBlk

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def diagU (a c : Kˣ) : GL (Fin 6) K :=
  ⟨Matrix.diagonal ![(a : K), (a : K), (c : K), ((a⁻¹ : Kˣ) : K), ((a⁻¹ : Kˣ) : K), ((c⁻¹ : Kˣ) : K)],
    Matrix.diagonal ![((a⁻¹ : Kˣ) : K), ((a⁻¹ : Kˣ) : K), ((c⁻¹ : Kˣ) : K), (a : K), (a : K), (c : K)],
    by
      rw [Matrix.diagonal_mul_diagonal]
      convert Matrix.diagonal_one using 2
      funext i
      fin_cases i <;> simp,
    by
      rw [Matrix.diagonal_mul_diagonal]
      convert Matrix.diagonal_one using 2
      funext i
      fin_cases i <;> simp⟩

theorem diagU_val (a c : Kˣ) :
    ((diagU a c : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      Matrix.diagonal ![(a : K), (a : K), (c : K), ((a⁻¹ : Kˣ) : K), ((a⁻¹ : Kˣ) : K),
        ((c⁻¹ : Kˣ) : K)] := rfl

@[expose] noncomputable def diagUHom : Kˣ × Kˣ →* GL (Fin 6) K where
  toFun ac := diagU ac.1 ac.2
  map_one' := by
    apply Units.ext
    rw [diagU_val, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' x y := by
    apply Units.ext
    rw [Units.val_mul, diagU_val, diagU_val, diagU_val, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [mul_comm]

theorem diagUHom_injective : Function.Injective (diagUHom (K := K)) := by
  rintro ⟨a, c⟩ ⟨a', c'⟩ h
  have h0 := congrArg (fun g : GL (Fin 6) K => ((g : Matrix (Fin 6) (Fin 6) K)) 0 0) h
  have h2 := congrArg (fun g : GL (Fin 6) K => ((g : Matrix (Fin 6) (Fin 6) K)) 2 2) h
  simp only [diagUHom, MonoidHom.coe_mk, OneHom.coe_mk, diagU_val, Matrix.diagonal_apply_eq] at h0 h2
  ext
  · simpa using h0
  · simpa using h2

abbrev mu3U (K : Type) [Field K] : Subgroup Kˣ := rootsOfUnity 3 K

@[expose] noncomputable def Fdiag (K : Type) [Field K] : Subgroup (GL (Fin 6) K) :=
  (diagUHom.comp (Subgroup.prod (mu3U K) (mu3U K)).subtype).range

@[expose] def emb3 (X : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  !![X 0 0, X 0 1, 0; X 1 0, X 1 1, 0; 0, 0, 1]

theorem emb3_mul (X Y : Matrix (Fin 2) (Fin 2) K) : emb3 (X * Y) = emb3 X * emb3 Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [emb3, Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_two]

theorem emb3_one : emb3 (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [emb3]

theorem det_emb3 (X : Matrix (Fin 2) (Fin 2) K) : (emb3 X).det = X.det := by
  rw [emb3, Matrix.det_fin_three, Matrix.det_fin_two]
  simp [Matrix.det_fin_two]

theorem zero_of_comm {a b c : K} (hab : a ≠ b) (h : c * b = a * c) : c = 0 := by
  have h' : c * (b - a) = 0 := by rw [mul_sub, h]; ring
  rcases mul_eq_zero.mp h' with h0 | h0
  · exact h0
  · exact absurd (sub_eq_zero.mp h0).symm hab

theorem centralizer_block (h : UnitaryFieldData p f K) {ζu : Kˣ}
    (hζ : IsPrimitiveRoot (ζu : K) 3)
    {x : GL (Fin 6) K} (hx : x ∈ gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K))
    (h1 : x * diagU ζu 1 = diagU ζu 1 * x) (h2 : x * diagU 1 ζu = diagU 1 ζu * x) :
    ∃ P : GL (Fin 3) K, x = Mh h P ∧ (P : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 ∧
      (P : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 ∧ (P : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧
      (P : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
  set ζ : K := (ζu : K) with hζdef
  have hn1 : ζ ≠ 1 := by
    simpa using hζ.pow_ne_one_of_pos_of_lt (l := 1) one_ne_zero (by norm_num)
  have hn2 : ζ⁻¹ ≠ 1 := by
    rw [ne_eq, inv_eq_one]
    exact hn1
  have hn3 : ζ ≠ ζ⁻¹ := by
    intro he
    have hz : ζ ≠ 0 := hζ.ne_zero (by norm_num)
    have h2 : ζ * ζ = 1 := by
      calc ζ * ζ = ζ * ζ⁻¹ := by rw [← he]
        _ = 1 := mul_inv_cancel₀ hz
    have h3 : ζ ^ 2 = 1 := by rw [pow_two]; exact h2
    exact hζ.pow_ne_one_of_pos_of_lt (l := 2) two_ne_zero (by norm_num) h3
  have hn3' : ζ⁻¹ ≠ ζ := fun he => hn3 he.symm
  have e1 : ∀ i j, (x : Matrix (Fin 6) (Fin 6) K) i j *
      (![ζ, ζ, 1, ζ⁻¹, ζ⁻¹, 1] : Fin 6 → K) j = (![ζ, ζ, 1, ζ⁻¹, ζ⁻¹, 1] : Fin 6 → K) i *
        (x : Matrix (Fin 6) (Fin 6) K) i j := by
    intro i j
    have := congrFun (congrFun (congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K)) h1) i) j
    simp only [Units.val_mul, diagU_val, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Units.val_inv_eq_inv_val, Units.val_one, inv_one] at this
    rw [← hζdef] at this
    exact this
  have e2 : ∀ i j, (x : Matrix (Fin 6) (Fin 6) K) i j *
      (![1, 1, ζ, 1, 1, ζ⁻¹] : Fin 6 → K) j = (![1, 1, ζ, 1, 1, ζ⁻¹] : Fin 6 → K) i *
        (x : Matrix (Fin 6) (Fin 6) K) i j := by
    intro i j
    have := congrFun (congrFun (congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K)) h2) i) j
    simp only [Units.val_mul, diagU_val, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Units.val_inv_eq_inv_val, Units.val_one, inv_one] at this
    rw [← hζdef] at this
    exact this
  set X := (x : Matrix (Fin 6) (Fin 6) K) with hXdef
  have z02 : X 0 2 = 0 := zero_of_comm (a := 1) (b := ζ) hn1.symm (by simpa using e2 0 2)
  have z12 : X 1 2 = 0 := zero_of_comm (a := 1) (b := ζ) hn1.symm (by simpa using e2 1 2)
  have z20 : X 2 0 = 0 := zero_of_comm (a := ζ) (b := 1) hn1 (by simpa using e2 2 0)
  have z21 : X 2 1 = 0 := zero_of_comm (a := ζ) (b := 1) hn1 (by simpa using e2 2 1)
  have z03 : X 0 3 = 0 := zero_of_comm (a := ζ) (b := ζ⁻¹) hn3 (by simpa using e1 0 3)
  have z04 : X 0 4 = 0 := zero_of_comm (a := ζ) (b := ζ⁻¹) hn3 (by simpa using e1 0 4)
  have z05 : X 0 5 = 0 := zero_of_comm (a := ζ) (b := 1) hn1 (by simpa using e1 0 5)
  have z13 : X 1 3 = 0 := zero_of_comm (a := ζ) (b := ζ⁻¹) hn3 (by simpa using e1 1 3)
  have z14 : X 1 4 = 0 := zero_of_comm (a := ζ) (b := ζ⁻¹) hn3 (by simpa using e1 1 4)
  have z15 : X 1 5 = 0 := zero_of_comm (a := ζ) (b := 1) hn1 (by simpa using e1 1 5)
  have z23 : X 2 3 = 0 := zero_of_comm (a := 1) (b := ζ⁻¹) hn2.symm (by simpa using e1 2 3)
  have z24 : X 2 4 = 0 := zero_of_comm (a := 1) (b := ζ⁻¹) hn2.symm (by simpa using e1 2 4)
  have z25 : X 2 5 = 0 := zero_of_comm (a := ζ) (b := ζ⁻¹) hn3 (by simpa using e2 2 5)
  have z30 : X 3 0 = 0 := zero_of_comm (a := ζ⁻¹) (b := ζ) hn3' (by simpa using e1 3 0)
  have z31 : X 3 1 = 0 := zero_of_comm (a := ζ⁻¹) (b := ζ) hn3' (by simpa using e1 3 1)
  have z32 : X 3 2 = 0 := zero_of_comm (a := ζ⁻¹) (b := 1) hn2 (by simpa using e1 3 2)
  have z40 : X 4 0 = 0 := zero_of_comm (a := ζ⁻¹) (b := ζ) hn3' (by simpa using e1 4 0)
  have z41 : X 4 1 = 0 := zero_of_comm (a := ζ⁻¹) (b := ζ) hn3' (by simpa using e1 4 1)
  have z42 : X 4 2 = 0 := zero_of_comm (a := ζ⁻¹) (b := 1) hn2 (by simpa using e1 4 2)
  have z50 : X 5 0 = 0 := zero_of_comm (a := 1) (b := ζ) hn1.symm (by simpa using e1 5 0)
  have z51 : X 5 1 = 0 := zero_of_comm (a := 1) (b := ζ) hn1.symm (by simpa using e1 5 1)
  have z52 : X 5 2 = 0 := zero_of_comm (a := ζ⁻¹) (b := ζ) hn3' (by simpa using e2 5 2)
  have hQ : Matrix.of (fun i j : Fin 3 => X (ie i) (jf j)) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      first
      | exact z03 | exact z04 | exact z05 | exact z13 | exact z14 | exact z15
      | exact z23 | exact z24 | exact z25
  have hR : Matrix.of (fun i j : Fin 3 => X (jf i) (ie j)) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      first
      | exact z30 | exact z31 | exact z32 | exact z40 | exact z41 | exact z42
      | exact z50 | exact z51 | exact z52
  set Pm : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i j => X (ie i) (ie j) with hPm
  set Sm : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i j => X (jf i) (jf j) with hSm
  have hxeq : X = blk Pm 0 0 Sm := by
    conv_lhs => rw [eq_blk_of X]
    rw [hQ, hR]
  have hunit : IsUnit (X.det) := (Matrix.isUnit_iff_isUnit_det _).mp (x.isUnit)
  have hdetP : Pm.det ≠ 0 := by
    have h1' : IsUnit (Pm.det * Sm.det) := by
      rw [← det_blk_diag, ← hxeq]
      exact hunit
    exact (isUnit_of_mul_isUnit_left h1').ne_zero
  set P : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero Pm hdetP with hPdef
  have hPval : (P : Matrix (Fin 3) (Fin 3) K) = Pm := rfl
  have hiso : (Pm.map h.bar)ᵀ * Sm = 1 := by
    have hx' := (mem_gramSU.mp hx).1
    rw [← hXdef, hxeq] at hx'
    exact hyp_block_isometry h Pm Sm hx'
  have hS : Sm = lowBlk h P := by
    have hinvL : lowBlk h P * (Pm.map h.bar)ᵀ = 1 := by
      have := lowBlk_mul_upper h P
      rw [hPval] at this
      exact this
    calc Sm = (Pm.map h.bar)ᵀ⁻¹ := (Matrix.inv_eq_right_inv hiso).symm
      _ = lowBlk h P := (Matrix.inv_eq_left_inv hinvL)
  refine ⟨P, ?_, ?_, ?_, ?_, ?_⟩
  · apply Units.ext
    show X = blk (P : Matrix (Fin 3) (Fin 3) K) 0 0 (lowBlk h P)
    rw [hxeq, hPval, ← hS]
  · rw [hPval]; exact z02
  · rw [hPval]; exact z12
  · rw [hPval]; exact z20
  · rw [hPval]; exact z21

theorem emb3_comm_diag (Y : Matrix (Fin 2) (Fin 2) K) (a c : K) :
    emb3 Y * Matrix.diagonal ![a, a, c] = Matrix.diagonal ![a, a, c] * emb3 Y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [emb3, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]
  all_goals ring

theorem det_ne_zero_of_GL {n : Type} [Fintype n] [DecidableEq n] (A : GL n K) :
    (A : Matrix n n K).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero

@[expose] noncomputable def emb3GL : GL (Fin 2) K →* GL (Fin 3) K where
  toFun A := Matrix.GeneralLinearGroup.mkOfDetNeZero (emb3 (A : Matrix (Fin 2) (Fin 2) K))
    (by rw [det_emb3]; exact det_ne_zero_of_GL A)
  map_one' := by
    apply Units.ext
    simp [emb3_one]
  map_mul' A B := by
    apply Units.ext
    simp [emb3_mul]

theorem emb3GL_val (A : GL (Fin 2) K) :
    ((emb3GL A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = emb3 (A : Matrix (Fin 2) (Fin 2) K) := rfl

@[expose] noncomputable def PsiGL (h : UnitaryFieldData p f K) : GL (Fin 2) K →* GL (Fin 6) K :=
  (MonoidHom.mk' (fun A : GL (Fin 3) K => Mh h A) (fun A B => Mh_mul h A B)).comp emb3GL

theorem PsiGL_apply (h : UnitaryFieldData p f K) (A : GL (Fin 2) K) :
    PsiGL h A = Mh h (emb3GL A) := rfl

@[expose] noncomputable def Psi (h : UnitaryFieldData p f K) :
    Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin 6) K :=
  (PsiGL h).comp (Matrix.SpecialLinearGroup.toGL)

theorem Psi_apply (h : UnitaryFieldData p f K) (X : Matrix.SpecialLinearGroup (Fin 2) K) :
    Psi h X = PsiGL h (Matrix.SpecialLinearGroup.toGL X) := rfl

theorem Psi_mem (h : UnitaryFieldData p f K) (X : Matrix.SpecialLinearGroup (Fin 2) K) :
    Psi h X ∈ gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K) := by
  rw [Psi_apply, PsiGL_apply]
  apply Mh_mem
  rw [emb3GL_val, det_emb3]
  exact X.2

theorem Psi_injective (h : UnitaryFieldData p f K) : Function.Injective (Psi h) := by
  rw [injective_iff_map_eq_one]
  intro X hX
  have hA : blk ((emb3GL (Matrix.SpecialLinearGroup.toGL X) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0
      (lowBlk h (emb3GL (Matrix.SpecialLinearGroup.toGL X))) = blk 1 0 0 1 := by
    rw [blk_one]
    have := congrArg Units.val hX
    rw [Psi_apply, PsiGL_apply] at this
    simpa [Mh_val, Units.val_one] using this
  have hE := (blk_inj hA).1
  rw [emb3GL_val] at hE
  have hX' : ((Matrix.SpecialLinearGroup.toGL X : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (X : Matrix (Fin 2) (Fin 2) K) := rfl
  rw [hX'] at hE
  have h00 : (X : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    have := congrFun (congrFun hE 0) 0; simpa [emb3] using this
  have h01 : (X : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    have := congrFun (congrFun hE 0) 1; simpa [emb3] using this
  have h10 : (X : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    have := congrFun (congrFun hE 1) 0; simpa [emb3] using this
  have h11 : (X : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    have := congrFun (congrFun hE 1) 1; simpa [emb3] using this
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]

theorem diagU_eq_blk (a c : Kˣ) :
    ((diagU a c : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      blk (Matrix.diagonal ![(a : K), (a : K), (c : K)]) 0 0
        (Matrix.diagonal ![((a⁻¹ : Kˣ) : K), ((a⁻¹ : Kˣ) : K), ((c⁻¹ : Kˣ) : K)]) := by
  rw [diagU_val, diag_blk]
  have h1 : (fun k : Fin 3 => (![(a : K), (a : K), (c : K), ((a⁻¹ : Kˣ) : K), ((a⁻¹ : Kˣ) : K),
      ((c⁻¹ : Kˣ) : K)] : Fin 6 → K) (ie k)) = ![(a : K), (a : K), (c : K)] := by
    funext k; fin_cases k <;> rfl
  have h2 : (fun k : Fin 3 => (![(a : K), (a : K), (c : K), ((a⁻¹ : Kˣ) : K), ((a⁻¹ : Kˣ) : K),
      ((c⁻¹ : Kˣ) : K)] : Fin 6 → K) (jf k)) =
      ![((a⁻¹ : Kˣ) : K), ((a⁻¹ : Kˣ) : K), ((c⁻¹ : Kˣ) : K)] := by
    funext k; fin_cases k <;> rfl
  rw [h1, h2]

@[expose] noncomputable def diagGL3 (a c : Kˣ) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![(a : K), (a : K), (c : K)])
    (by
      rw [Matrix.det_diagonal, Fin.prod_univ_three]
      simp)

theorem diagGL3_val (a c : Kˣ) :
    ((diagGL3 a c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![(a : K), (a : K), (c : K)] := rfl

theorem diagGL3_inv_val (a c : Kˣ) :
    (((diagGL3 a c)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![((a⁻¹ : Kˣ) : K), ((a⁻¹ : Kˣ) : K), ((c⁻¹ : Kˣ) : K)] := by
  rw [Matrix.coe_units_inv, diagGL3_val]
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal]
  have : ∀ i : Fin 3, (![((a⁻¹ : Kˣ) : K), ((a⁻¹ : Kˣ) : K), ((c⁻¹ : Kˣ) : K)] : Fin 3 → K) i *
      (![(a : K), (a : K), (c : K)] : Fin 3 → K) i = 1 := by
    intro i
    fin_cases i <;> simp
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  exact this i

theorem diagU_eq_Mh (h : UnitaryFieldData p f K) (hbar : ∀ x : K, x ^ 3 = 1 → h.bar x = x)
    {a c : Kˣ} (ha : a ^ 3 = 1) (hc : c ^ 3 = 1) :
    diagU a c = Mh h (diagGL3 a c) := by
  apply Units.ext
  rw [diagU_eq_blk, Mh_val, diagGL3_val]
  congr 1
  unfold lowBlk
  rw [diagGL3_inv_val, Matrix.diagonal_map, Matrix.diagonal_transpose]
  · congr 1
    funext i
    have ha' : ((a⁻¹ : Kˣ) : K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, inv_pow, ha, inv_one, Units.val_one]
    have hc' : ((c⁻¹ : Kˣ) : K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, inv_pow, hc, inv_one, Units.val_one]
    have ha0 : ((a : Kˣ) : K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ha, Units.val_one]
    have hc0 : ((c : Kˣ) : K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
    fin_cases i <;> simp [hbar _ ha0, hbar _ hc0, hbar _ ha', hbar _ hc']
  · exact map_zero h.bar

theorem Psi_comm_diagU (h : UnitaryFieldData p f K) (hbar : ∀ x : K, x ^ 3 = 1 → h.bar x = x)
    (X : Matrix.SpecialLinearGroup (Fin 2) K) {a c : Kˣ} (ha : a ^ 3 = 1) (hc : c ^ 3 = 1) :
    Psi h X * diagU a c = diagU a c * Psi h X := by
  rw [diagU_eq_Mh h hbar ha hc, Psi_apply, PsiGL_apply]
  rw [← Mh_mul, ← Mh_mul]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, emb3GL_val, diagGL3_val]
  exact emb3_comm_diag (K := K) _ _ _

theorem block_factor (P : GL (Fin 3) K) (h02 : (P : Matrix (Fin 3) (Fin 3) K) 0 2 = 0)
    (h12 : (P : Matrix (Fin 3) (Fin 3) K) 1 2 = 0) (h20 : (P : Matrix (Fin 3) (Fin 3) K) 2 0 = 0)
    (h21 : (P : Matrix (Fin 3) (Fin 3) K) 2 1 = 0) :
    (P : Matrix (Fin 3) (Fin 3) K) = emb3 !![(P : Matrix (Fin 3) (Fin 3) K) 0 0,
      (P : Matrix (Fin 3) (Fin 3) K) 0 1; (P : Matrix (Fin 3) (Fin 3) K) 1 0,
      (P : Matrix (Fin 3) (Fin 3) K) 1 1] * Matrix.diagonal ![1, 1, (P : Matrix (Fin 3) (Fin 3) K) 2 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [emb3, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, h02, h12, h20, h21]

@[expose] noncomputable def embSL3 (X : Matrix.SpecialLinearGroup (Fin 2) K) : GL (Fin 3) K :=
  emb3GL (Matrix.SpecialLinearGroup.toGL X)

theorem embSL3_val (X : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((embSL3 X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = emb3 (X : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem diagGL3_comm_emb (X : Matrix.SpecialLinearGroup (Fin 2) K) (a c : Kˣ) :
    diagGL3 a c * embSL3 X = embSL3 X * diagGL3 a c := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, diagGL3_val, embSL3_val]
  exact (emb3_comm_diag (K := K) _ _ _).symm

theorem Psi_normal (h : UnitaryFieldData p f K) (P : GL (Fin 3) K)
    (h02 : (P : Matrix (Fin 3) (Fin 3) K) 0 2 = 0) (h12 : (P : Matrix (Fin 3) (Fin 3) K) 1 2 = 0)
    (h20 : (P : Matrix (Fin 3) (Fin 3) K) 2 0 = 0) (h21 : (P : Matrix (Fin 3) (Fin 3) K) 2 1 = 0)
    (X : Matrix.SpecialLinearGroup (Fin 2) K) :
    ∃ X' : Matrix.SpecialLinearGroup (Fin 2) K, Mh h P * Psi h X = Psi h X' * Mh h P := by
  have hdetP : (P : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := det_ne_zero_of_GL P
  have hfac := block_factor P h02 h12 h20 h21
  have key : (P : Matrix (Fin 3) (Fin 3) K).det =
      Matrix.det !![(P : Matrix (Fin 3) (Fin 3) K) 0 0, (P : Matrix (Fin 3) (Fin 3) K) 0 1;
        (P : Matrix (Fin 3) (Fin 3) K) 1 0, (P : Matrix (Fin 3) (Fin 3) K) 1 1] *
        (P : Matrix (Fin 3) (Fin 3) K) 2 2 := by
    conv_lhs => rw [hfac]
    rw [Matrix.det_mul, det_emb3, Matrix.det_diagonal, Fin.prod_univ_three]
    simp
  have hdet2 : Matrix.det !![(P : Matrix (Fin 3) (Fin 3) K) 0 0, (P : Matrix (Fin 3) (Fin 3) K) 0 1;
      (P : Matrix (Fin 3) (Fin 3) K) 1 0, (P : Matrix (Fin 3) (Fin 3) K) 1 1] ≠ 0 := by
    intro h0; apply hdetP; rw [key, h0, zero_mul]
  have hc : (P : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 := by
    intro h0; apply hdetP; rw [key, h0, mul_zero]
  set P2 : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(P : Matrix (Fin 3) (Fin 3) K) 0 0, (P : Matrix (Fin 3) (Fin 3) K) 0 1;
      (P : Matrix (Fin 3) (Fin 3) K) 1 0, (P : Matrix (Fin 3) (Fin 3) K) 1 1] hdet2 with hP2
  set c : Kˣ := Units.mk0 ((P : Matrix (Fin 3) (Fin 3) K) 2 2) hc with hcdef
  have hcval : ((c : Kˣ) : K) = (P : Matrix (Fin 3) (Fin 3) K) 2 2 := rfl
  have hP2val : ((P2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![(P : Matrix (Fin 3) (Fin 3) K) 0 0, (P : Matrix (Fin 3) (Fin 3) K) 0 1;
        (P : Matrix (Fin 3) (Fin 3) K) 1 0, (P : Matrix (Fin 3) (Fin 3) K) 1 1] := rfl
  have hPfac : P = emb3GL P2 * diagGL3 1 c := by
    apply Units.ext
    rw [Units.val_mul, emb3GL_val, diagGL3_val, hP2val, hcval]
    exact hfac
  have hMh : Mh h P = PsiGL h P2 * Mh h (diagGL3 1 c) := by
    rw [hPfac, Mh_mul, PsiGL_apply]
  have hcomm : Mh h (diagGL3 1 c) * Psi h X = Psi h X * Mh h (diagGL3 1 c) := by
    have hX : Psi h X = Mh h (embSL3 X) := rfl
    rw [hX, ← Mh_mul, ← Mh_mul, diagGL3_comm_emb X]
  set X'' : GL (Fin 2) K := P2 * Matrix.SpecialLinearGroup.toGL X * P2⁻¹ with hX''
  have hdet'' : (X'' : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    have h1 : ((P2⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det *
        ((P2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    have h2 : (X'' : Matrix (Fin 2) (Fin 2) K) = ((P2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        (X : Matrix (Fin 2) (Fin 2) K) * ((P2⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := rfl
    rw [h2, Matrix.det_mul, Matrix.det_mul, X.2, mul_one, mul_comm]
    exact h1
  set X' : Matrix.SpecialLinearGroup (Fin 2) K := ⟨(X'' : Matrix (Fin 2) (Fin 2) K), hdet''⟩ with hX'
  have hX'toGL : Matrix.SpecialLinearGroup.toGL X' = X'' := Units.ext rfl
  refine ⟨X', ?_⟩
  have hPX : P2 * Matrix.SpecialLinearGroup.toGL X = X'' * P2 := by
    rw [hX'']; group
  calc Mh h P * Psi h X = (PsiGL h P2 * Mh h (diagGL3 1 c)) * Psi h X := by rw [hMh]
    _ = PsiGL h P2 * (Mh h (diagGL3 1 c) * Psi h X) := by rw [mul_assoc]
    _ = PsiGL h P2 * (Psi h X * Mh h (diagGL3 1 c)) := by rw [hcomm]
    _ = PsiGL h (P2 * Matrix.SpecialLinearGroup.toGL X) * Mh h (diagGL3 1 c) := by
        rw [map_mul, ← mul_assoc, Psi_apply]
    _ = PsiGL h (X'' * P2) * Mh h (diagGL3 1 c) := by rw [hPX]
    _ = (PsiGL h X'' * PsiGL h P2) * Mh h (diagGL3 1 c) := by rw [map_mul]
    _ = PsiGL h X'' * (PsiGL h P2 * Mh h (diagGL3 1 c)) := by rw [mul_assoc]
    _ = PsiGL h X'' * Mh h P := by rw [hMh]
    _ = Psi h X' * Mh h P := by rw [Psi_apply, hX'toGL]

theorem Mh_mem_of_bar (h : UnitaryFieldData p f K) (A : GL (Fin 3) K)
    (hA : h.bar (A : Matrix (Fin 3) (Fin 3) K).det = (A : Matrix (Fin 3) (Fin 3) K).det) :
    Mh h A ∈ gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K) := by
  rw [mem_gramSU]
  refine ⟨?_, ?_⟩
  · have hY : ((A : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * lowBlk h A = 1 :=
      upper_mul_lowBlk h A
    have hZ : ((lowBlk h A).map h.bar)ᵀ * (A : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [lowBlk_map_bar h A, GL_inv_mul_mat A]
    have hv : ((Mh h A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        blk (A : Matrix (Fin 3) (Fin 3) K) 0 0 (lowBlk h A) := rfl
    rw [hv, blk_map, blk_transpose, hypJ, blk_mul, blk_mul]
    simp only [map_zero_bar h, transpose_zero, mul_zero, zero_mul, add_zero, zero_add, mul_one,
      hY, hZ]
  · show (blk (A : Matrix (Fin 3) (Fin 3) K) 0 0 (lowBlk h A)).det = 1
    rw [det_blk_diag, det_lowBlk]
    have hA0 : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := det_ne_zero_of_GL A
    have hinv : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
        ((A : Matrix (Fin 3) (Fin 3) K).det)⁻¹ := by
      have h1 := congrArg Matrix.det (GL_inv_mul_mat A)
      rw [Matrix.det_mul, Matrix.det_one] at h1
      exact eq_inv_of_mul_eq_one_left h1
    rw [hinv, map_inv₀, hA, mul_inv_cancel₀ hA0]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
