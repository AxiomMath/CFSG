module

public import CFSG.LieType.Universal.Unitary.Comparison

public section

namespace CFSG.ClassicalInvolution.Q3

open Matrix CFSG.LieType.Universal.Unitary

section Generic

variable {E : Type} [Field E] (σ : E ≃+* E) {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def cT {m n : Type} (A : Matrix m n E) : Matrix n m E := (A.map σ)ᵀ

theorem cT_mul {l m n : Type} [Fintype m] (A : Matrix l m E) (B : Matrix m n E) :
    cT σ (A * B) = cT σ B * cT σ A := by
  simp only [cT, Matrix.map_mul, transpose_mul]

omit [Fintype ι] in
theorem cT_one : cT σ (1 : Matrix ι ι E) = 1 := by simp [cT]

theorem cT_conjTr {n : ℕ} (A : Matrix (Fin n) (Fin n) E) : cT σ A = conjTr σ A := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem cT_smul (c : E) (A : Matrix ι ι E) : cT σ (c • A) = σ c • cT σ A := by
  ext i j
  simp [cT]

@[expose] def SUG (G : Matrix ι ι E) : Subgroup (GL ι E) where
  carrier := {x | (x : Matrix ι ι E).det = 1 ∧ cT σ (x : Matrix ι ι E) * G * (x : Matrix ι ι E) = G}
  mul_mem' {A B} hA hB := by
    refine ⟨by rw [Units.val_mul, det_mul, hA.1, hB.1, one_mul], ?_⟩
    have e : cT σ ((A : Matrix ι ι E) * (B : Matrix ι ι E)) * G *
        ((A : Matrix ι ι E) * (B : Matrix ι ι E)) =
        cT σ (B : Matrix ι ι E) * (cT σ (A : Matrix ι ι E) * G * (A : Matrix ι ι E)) *
          (B : Matrix ι ι E) := by
      rw [cT_mul]
      simp only [Matrix.mul_assoc]
    rw [Units.val_mul, e, hA.2, hB.2]
  one_mem' := ⟨by simp, by simp [cT_one]⟩
  inv_mem' {A} hA := by
    have hAB : (A : Matrix ι ι E) * ((A⁻¹ : GL ι E) : Matrix ι ι E) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    refine ⟨?_, ?_⟩
    · have := congrArg Matrix.det hAB
      rw [det_mul, det_one, hA.1, one_mul] at this
      exact this
    · have key : cT σ ((A⁻¹ : GL ι E) : Matrix ι ι E) *
          (cT σ (A : Matrix ι ι E) * G * (A : Matrix ι ι E)) *
            ((A⁻¹ : GL ι E) : Matrix ι ι E) =
          cT σ ((A : Matrix ι ι E) * ((A⁻¹ : GL ι E) : Matrix ι ι E)) * G *
            ((A : Matrix ι ι E) * ((A⁻¹ : GL ι E) : Matrix ι ι E)) := by
        rw [cT_mul]
        simp only [Matrix.mul_assoc]
      rw [hA.2, hAB, cT_one, Matrix.one_mul, Matrix.mul_one] at key
      exact key

theorem mem_SUG {G : Matrix ι ι E} {x : GL ι E} :
    x ∈ SUG σ G ↔ (x : Matrix ι ι E).det = 1 ∧
      cT σ (x : Matrix ι ι E) * G * (x : Matrix ι ι E) = G := Iff.rfl

theorem SUG_antidiag (n : ℕ) : SUG σ (antidiag n : Matrix (Fin n) (Fin n) E) = SU σ n :=
  Subgroup.ext fun _ => Iff.rfl

theorem SUG_one (n : ℕ) : SUG σ (1 : Matrix (Fin n) (Fin n) E) = SUid σ n :=
  Subgroup.ext fun x => by
    simp only [mem_SUG, SUid, Subgroup.mem_mk, Matrix.mul_one]
    rfl

end Generic

section Conj

variable {E : Type} [Field E] (σ : E ≃+* E) {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι']
  [DecidableEq ι']

@[expose] def conjMat (Q : Matrix ι ι' E) (Q' : Matrix ι' ι E) (h1 : Q * Q' = 1)
    (h2 : Q' * Q = 1) : Matrix ι' ι' E ≃* Matrix ι ι E where
  toFun x := Q * x * Q'
  invFun y := Q' * y * Q
  left_inv x := by
    show Q' * (Q * x * Q') * Q = x
    have : Q' * (Q * x * Q') * Q = (Q' * Q) * x * (Q' * Q) := by simp only [Matrix.mul_assoc]
    rw [this, h2, Matrix.one_mul, Matrix.mul_one]
  right_inv y := by
    show Q * (Q' * y * Q) * Q' = y
    have : Q * (Q' * y * Q) * Q' = (Q * Q') * y * (Q * Q') := by simp only [Matrix.mul_assoc]
    rw [this, h1, Matrix.one_mul, Matrix.mul_one]
  map_mul' x y := by
    show Q * (x * y) * Q' = (Q * x * Q') * (Q * y * Q')
    have : (Q * x * Q') * (Q * y * Q') = Q * x * (Q' * Q) * y * Q' := by
      simp only [Matrix.mul_assoc]
    rw [this, h2, Matrix.mul_one]
    simp only [Matrix.mul_assoc]

theorem conjMat_apply (Q : Matrix ι ι' E) (Q' : Matrix ι' ι E) (h1 : Q * Q' = 1) (h2 : Q' * Q = 1)
    (x : Matrix ι' ι' E) : conjMat Q Q' h1 h2 x = Q * x * Q' := rfl

theorem fintype_card_eq_of_mul_eq_one {Q : Matrix ι ι' E} {Q' : Matrix ι' ι E} (h1 : Q * Q' = 1)
    (h2 : Q' * Q = 1) : Fintype.card ι' = Fintype.card ι := by
  have e : (ι' → E) ≃ₗ[E] (ι → E) :=
    LinearEquiv.ofLinearMap (Matrix.mulVecLin Q) (Matrix.mulVecLin Q')
      (by rw [← Matrix.mulVecLin_mul, h1, Matrix.mulVecLin_one])
      (by rw [← Matrix.mulVecLin_mul, h2, Matrix.mulVecLin_one])
  have := e.finrank_eq
  simpa [Module.finrank_fintype_fun_eq_card] using this

theorem det_conjMat {Q : Matrix ι ι' E} {Q' : Matrix ι' ι E} (h1 : Q * Q' = 1) (h2 : Q' * Q = 1)
    (x : Matrix ι' ι' E) : (Q * x * Q').det = x.det := by
  obtain ⟨e⟩ := Fintype.card_eq.mp (fintype_card_eq_of_mul_eq_one h1 h2)
  have hQQ : Q.submatrix id e.symm * Q'.submatrix e.symm id = 1 := by
    rw [Matrix.submatrix_mul_equiv, h1]
    rfl
  have hx : Q.submatrix id e.symm * x.submatrix e.symm e.symm * Q'.submatrix e.symm id =
      Q * x * Q' := by
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    rfl
  rw [← hx, Matrix.det_mul, Matrix.det_mul, Matrix.det_submatrix_equiv_self]
  have := congrArg Matrix.det hQQ
  rw [Matrix.det_mul, Matrix.det_one] at this
  calc (Q.submatrix id e.symm).det * x.det * (Q'.submatrix e.symm id).det
      = ((Q.submatrix id e.symm).det * (Q'.submatrix e.symm id).det) * x.det := by ring
    _ = x.det := by rw [this, one_mul]

@[expose] def conjGL (Q : Matrix ι ι' E) (Q' : Matrix ι' ι E) (h1 : Q * Q' = 1)
    (h2 : Q' * Q = 1) : GL ι' E ≃* GL ι E :=
  Units.mapEquiv (conjMat Q Q' h1 h2)

theorem coe_conjGL (Q : Matrix ι ι' E) (Q' : Matrix ι' ι E) (h1 : Q * Q' = 1) (h2 : Q' * Q = 1)
    (x : GL ι' E) :
    ((conjGL Q Q' h1 h2 x : GL ι E) : Matrix ι ι E) = Q * (x : Matrix ι' ι' E) * Q' := rfl

theorem coe_conjGL_symm (Q : Matrix ι ι' E) (Q' : Matrix ι' ι E) (h1 : Q * Q' = 1)
    (h2 : Q' * Q = 1) (y : GL ι E) :
    (((conjGL Q Q' h1 h2).symm y : GL ι' E) : Matrix ι' ι' E) = Q' * (y : Matrix ι ι E) * Q := rfl

theorem conjGL_mem_SUG_iff {Q : Matrix ι ι' E} {Q' : Matrix ι' ι E} (h1 : Q * Q' = 1)
    (h2 : Q' * Q = 1) {G : Matrix ι ι E} {M : Matrix ι' ι' E} (hM : cT σ Q * G * Q = M)
    (x : GL ι' E) : conjGL Q Q' h1 h2 x ∈ SUG σ G ↔ x ∈ SUG σ M := by
  rw [mem_SUG, mem_SUG, coe_conjGL, det_conjMat h1 h2]
  refine and_congr_right fun _ => ?_
  have hc1 : cT σ Q' * cT σ Q = 1 := by rw [← cT_mul, h1, cT_one]
  set X : Matrix ι' ι' E := (x : Matrix ι' ι' E) with hX
  set Y : Matrix ι ι E := Q * X * Q' with hY
  have hYQ : Y * Q = Q * X := by
    rw [hY, Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]
  constructor
  · intro h
    calc cT σ X * M * X = cT σ (Q * X) * G * (Q * X) := by
          rw [← hM, cT_mul]
          simp only [Matrix.mul_assoc]
      _ = cT σ (Y * Q) * G * (Y * Q) := by rw [hYQ]
      _ = cT σ Q * (cT σ Y * G * Y) * Q := by
          rw [cT_mul]
          simp only [Matrix.mul_assoc]
      _ = M := by rw [h, ← hM]
  · intro h
    calc cT σ Y * G * Y = cT σ Q' * (cT σ X * (cT σ Q * G * Q) * X) * Q' := by
          rw [hY, cT_mul, cT_mul]
          simp only [Matrix.mul_assoc]
      _ = cT σ Q' * M * Q' := by rw [hM, h]
      _ = (cT σ Q' * cT σ Q) * G * (Q * Q') := by
          rw [← hM]
          simp only [Matrix.mul_assoc]
      _ = G := by rw [hc1, h1, Matrix.one_mul, Matrix.mul_one]

@[expose] noncomputable def conjSUG {Q : Matrix ι ι' E} {Q' : Matrix ι' ι E} (h1 : Q * Q' = 1)
    (h2 : Q' * Q = 1) {G : Matrix ι ι E} {M : Matrix ι' ι' E} (hM : cT σ Q * G * Q = M) :
    SUG σ M ≃* SUG σ G :=
  (MulEquiv.subgroupMap (conjGL Q Q' h1 h2) (SUG σ M)).trans
    (MulEquiv.subgroupCongr (by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (conjGL_mem_SUG_iff σ h1 h2 hM x).mpr hx
      · intro hy
        exact ⟨(conjGL Q Q' h1 h2).symm y,
          (conjGL_mem_SUG_iff σ h1 h2 hM _).mp (by simpa using hy), by simp⟩))

theorem coe_conjSUG {Q : Matrix ι ι' E} {Q' : Matrix ι' ι E} (h1 : Q * Q' = 1)
    (h2 : Q' * Q = 1) {G : Matrix ι ι E} {M : Matrix ι' ι' E} (hM : cT σ Q * G * Q = M)
    (x : SUG σ M) :
    (((conjSUG σ h1 h2 hM x : SUG σ G) : GL ι E) : Matrix ι ι E) =
      Q * (((x : SUG σ M) : GL ι' E) : Matrix ι' ι' E) * Q' := rfl

end Conj

end CFSG.ClassicalInvolution.Q3
