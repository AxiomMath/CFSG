module

public import CFSG.LieType.Universal.Unitary.Comparison

public section

namespace CFSG.LieType.Steinberg

open Matrix CFSG.LieType.Universal.Unitary

section Gram

variable {F : Type*} [Field F] (τ : F →+* F) {n : ℕ}

@[expose] def ctr (A : Matrix (Fin n) (Fin n) F) : Matrix (Fin n) (Fin n) F :=
  (A.map τ)ᵀ

theorem ctr_mul (A B : Matrix (Fin n) (Fin n) F) : ctr τ (A * B) = ctr τ B * ctr τ A := by
  simp only [ctr, Matrix.map_mul, transpose_mul]

theorem ctr_one : ctr τ (1 : Matrix (Fin n) (Fin n) F) = 1 := by
  simp [ctr]

theorem ctr_submatrix (A : Matrix (Fin n) (Fin n) F) (e : Fin n ≃ Fin n) :
    ctr τ (A.submatrix e e) = (ctr τ A).submatrix e e :=
  rfl

private theorem val_mul_val_inv (P : GL (Fin n) F) :
    (P : Matrix (Fin n) (Fin n) F) * ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

private theorem val_inv_mul_val (P : GL (Fin n) F) :
    ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

@[expose] def SUgram (G : Matrix (Fin n) (Fin n) F) : Subgroup (GL (Fin n) F) where
  carrier := {A | (A : Matrix (Fin n) (Fin n) F).det = 1 ∧
    ctr τ (A : Matrix (Fin n) (Fin n) F) * G * (A : Matrix (Fin n) (Fin n) F) = G}
  mul_mem' {A B} hA hB := by
    refine ⟨by rw [Units.val_mul, det_mul, hA.1, hB.1, one_mul], ?_⟩
    rw [Units.val_mul, ctr_mul]
    calc ctr τ (B : Matrix (Fin n) (Fin n) F) * ctr τ (A : Matrix (Fin n) (Fin n) F) * G *
          ((A : Matrix (Fin n) (Fin n) F) * B)
        = ctr τ (B : Matrix (Fin n) (Fin n) F) *
            (ctr τ (A : Matrix (Fin n) (Fin n) F) * G * A) * B := by
          simp only [Matrix.mul_assoc]
      _ = G := by rw [hA.2, hB.2]
  one_mem' := ⟨by simp, by simp [ctr_one]⟩
  inv_mem' {A} hA := by
    refine ⟨?_, ?_⟩
    · have := congrArg Matrix.det (val_mul_val_inv A)
      rw [det_mul, det_one, hA.1, one_mul] at this
      exact this
    · calc ctr τ ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * G * ↑(A⁻¹ : GL (Fin n) F)
          = ctr τ ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
              (ctr τ (A : Matrix (Fin n) (Fin n) F) * G * A) * ↑(A⁻¹ : GL (Fin n) F) := by
            rw [hA.2]
        _ = ctr τ ((A : Matrix (Fin n) (Fin n) F) * ↑(A⁻¹ : GL (Fin n) F)) * G *
              ((A : Matrix (Fin n) (Fin n) F) * ↑(A⁻¹ : GL (Fin n) F)) := by
            rw [ctr_mul]
            simp only [Matrix.mul_assoc]
        _ = G := by rw [val_mul_val_inv, ctr_one, Matrix.one_mul, Matrix.mul_one]

variable {τ}

theorem mem_SUgram {G : Matrix (Fin n) (Fin n) F} {A : GL (Fin n) F} :
    A ∈ SUgram τ G ↔ (A : Matrix (Fin n) (Fin n) F).det = 1 ∧
      ctr τ (A : Matrix (Fin n) (Fin n) F) * G * (A : Matrix (Fin n) (Fin n) F) = G :=
  Iff.rfl

theorem SUgram_antidiag (σ : F ≃+* F) : SUgram σ.toRingHom (antidiag n) = SU σ n :=
  Subgroup.ext fun _ => Iff.rfl

theorem SUgram_one (σ : F ≃+* F) : SUgram σ.toRingHom (1 : Matrix (Fin n) (Fin n) F) =
    SUid σ n :=
  Subgroup.ext fun A => by
    rw [mem_SUgram, mem_SUid, Matrix.mul_one]
    rfl

@[expose] noncomputable def gramEquiv {G₁ G₂ : Matrix (Fin n) (Fin n) F} (P : GL (Fin n) F)
    (hP : ctr τ (P : Matrix (Fin n) (Fin n) F) * G₂ * (P : Matrix (Fin n) (Fin n) F) = G₁) :
    SUgram τ G₂ ≃* SUgram τ G₁ where
  toFun A := ⟨P⁻¹ * A * P, by
    obtain ⟨hdet, hiso⟩ := A.2
    set Pm := (P : Matrix (Fin n) (Fin n) F)
    set Pi := ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
    set Am := ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hdet, mul_one, ← det_mul,
        val_inv_mul_val, det_one]
    · rw [Units.val_mul, Units.val_mul, ← hP]
      calc ctr τ (Pi * Am * Pm) * (ctr τ Pm * G₂ * Pm) * (Pi * Am * Pm)
          = ctr τ Pm * ctr τ Am * (ctr τ (Pm * Pi) * G₂ * (Pm * Pi)) * Am * Pm := by
            simp only [ctr_mul, Matrix.mul_assoc]
        _ = ctr τ Pm * (ctr τ Am * G₂ * Am) * Pm := by
            rw [val_mul_val_inv, ctr_one, Matrix.one_mul, Matrix.mul_one]
            simp only [Matrix.mul_assoc]
        _ = ctr τ Pm * G₂ * Pm := by rw [hiso]⟩
  invFun B := ⟨P * B * P⁻¹, by
    obtain ⟨hdet, hiso⟩ := B.2
    set Pm := (P : Matrix (Fin n) (Fin n) F)
    set Pi := ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
    set Bm := ((B : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hdet, mul_one, ← det_mul,
        val_mul_val_inv, det_one]
    · rw [Units.val_mul, Units.val_mul]
      calc ctr τ (Pm * Bm * Pi) * G₂ * (Pm * Bm * Pi)
          = ctr τ Pi * (ctr τ Bm * (ctr τ Pm * G₂ * Pm) * Bm) * Pi := by
            simp only [ctr_mul, Matrix.mul_assoc]
        _ = ctr τ Pi * (ctr τ Pm * G₂ * Pm) * Pi := by rw [hP, hiso]
        _ = ctr τ (Pm * Pi) * G₂ * (Pm * Pi) := by simp only [ctr_mul, Matrix.mul_assoc]
        _ = G₂ := by rw [val_mul_val_inv, ctr_one, Matrix.one_mul, Matrix.mul_one]⟩
  left_inv A := Subtype.ext (by simp [mul_assoc])
  right_inv B := Subtype.ext (by simp [mul_assoc])
  map_mul' A B := Subtype.ext (by simp [mul_assoc])

theorem coe_gramEquiv {G₁ G₂ : Matrix (Fin n) (Fin n) F} (P : GL (Fin n) F)
    (hP : ctr τ (P : Matrix (Fin n) (Fin n) F) * G₂ * (P : Matrix (Fin n) (Fin n) F) = G₁)
    (A : SUgram τ G₂) : ((gramEquiv P hP A : SUgram τ G₁) : GL (Fin n) F) = P⁻¹ * A * P :=
  rfl

@[expose] def reindexGL (e : Fin n ≃ Fin n) (A : GL (Fin n) F) : GL (Fin n) F :=
  ⟨(A : Matrix (Fin n) (Fin n) F).submatrix e e,
    ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).submatrix e e,
    by rw [submatrix_mul_equiv, val_mul_val_inv, submatrix_one_equiv],
    by rw [submatrix_mul_equiv, val_inv_mul_val, submatrix_one_equiv]⟩

theorem coe_reindexGL (e : Fin n ≃ Fin n) (A : GL (Fin n) F) :
    ((reindexGL e A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (A : Matrix (Fin n) (Fin n) F).submatrix e e :=
  rfl

theorem reindexGL_mem {G : Matrix (Fin n) (Fin n) F} (e : Fin n ≃ Fin n) {A : GL (Fin n) F}
    (hA : A ∈ SUgram τ G) : reindexGL e A ∈ SUgram τ (G.submatrix e e) := by
  refine ⟨by rw [coe_reindexGL, det_submatrix_equiv_self, hA.1], ?_⟩
  rw [coe_reindexGL, ctr_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, hA.2]

@[expose] noncomputable def gramReindexEquiv (e : Fin n ≃ Fin n)
    (G : Matrix (Fin n) (Fin n) F) : SUgram τ G ≃* SUgram τ (G.submatrix e e) where
  toFun A := ⟨reindexGL e A, reindexGL_mem e A.2⟩
  invFun B := ⟨reindexGL e.symm B, by
    have h := reindexGL_mem e.symm B.2
    rwa [submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id] at h⟩
  left_inv A := Subtype.ext (Units.ext (by
    change (((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).submatrix e e).submatrix e.symm
      e.symm = _
    rw [submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id]))
  right_inv B := Subtype.ext (Units.ext (by
    change (((B : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).submatrix e.symm e.symm).submatrix
      e e = _
    rw [submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id]))
  map_mul' A B := Subtype.ext (Units.ext (by
    change (((A * B : SUgram τ G) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).submatrix e e =
      ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).submatrix e e *
        ((B : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).submatrix e e
    rw [submatrix_mul_equiv]
    rfl))

end Gram

section Block

variable (F : Type*) [Field F]

@[expose] def blockJ (r ε : ℕ) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) F :=
  Matrix.of fun i j =>
    if (i : ℕ) < r then (if (j : ℕ) = i + r + ε then 1 else 0)
    else if (i : ℕ) < r + ε then (if (j : ℕ) = i then 1 else 0)
    else (if (j : ℕ) + r + ε = i then 1 else 0)

@[expose] def blockPermFun (r ε : ℕ) (i : Fin (2 * r + ε)) : Fin (2 * r + ε) :=
  if h : (i : ℕ) < r + ε then i else ⟨3 * r + 2 * ε - 1 - i, by have := i.isLt; omega⟩

theorem val_blockPermFun (r ε : ℕ) (i : Fin (2 * r + ε)) :
    (blockPermFun r ε i : ℕ) = if (i : ℕ) < r + ε then (i : ℕ) else 3 * r + 2 * ε - 1 - i := by
  unfold blockPermFun
  split_ifs <;> rfl

theorem blockPermFun_involutive (r ε : ℕ) : Function.Involutive (blockPermFun r ε) := by
  intro i
  apply Fin.ext
  have hi := i.isLt
  rw [val_blockPermFun, val_blockPermFun]
  split_ifs <;> omega

@[expose] def blockPerm (r ε : ℕ) : Equiv.Perm (Fin (2 * r + ε)) :=
  (blockPermFun_involutive r ε).toPerm _

theorem antidiag_submatrix_blockPerm {r ε : ℕ} (hε : ε ≤ 1) :
    (antidiag (2 * r + ε) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) F).submatrix
      (blockPerm r ε) (blockPerm r ε) = blockJ F r ε := by
  ext i j
  simp only [blockPerm, Function.Involutive.coe_toPerm, submatrix_apply, antidiag, of_apply,
    blockJ, Fin.ext_iff, Fin.val_rev, val_blockPermFun]
  have hi := i.isLt
  have hj := j.isLt
  split_ifs
  all_goals first | rfl | omega

end Block

end CFSG.LieType.Steinberg
