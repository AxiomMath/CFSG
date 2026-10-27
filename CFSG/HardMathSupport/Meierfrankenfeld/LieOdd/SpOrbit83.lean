module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitCount
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open Matrix

abbrev X3 : Type := Fin 10 → ZMod 3

@[expose] def pr : Fin 10 → Fin 4 × Fin 4 :=
  ![(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (3, 3)]

@[expose] def cidx (i j : Fin 4) : Fin 10 :=
  (![![0, 1, 2, 3], ![1, 4, 5, 6], ![2, 5, 7, 8], ![3, 6, 8, 9]] : Fin 4 → Fin 4 → Fin 10) i j

theorem cidx_comm (i j : Fin 4) : cidx i j = cidx j i := by
  revert i j; decide

theorem cidx_pr : ∀ i j : Fin 4, pr (cidx i j) = (i, j) ∨ pr (cidx i j) = (j, i) := by
  decide

@[expose] def symMat (x : X3) : Matrix (Fin 4) (Fin 4) (ZMod 3) := Matrix.of fun i j => x (cidx i j)

theorem symMat_transpose (x : X3) : (symMat x)ᵀ = symMat x := by
  ext i j
  simp [symMat, cidx_comm i j]

theorem symMat_add (x y : X3) : symMat (x + y) = symMat x + symMat y := by
  ext i j; simp [symMat]

theorem symMat_smul (c : ZMod 3) (x : X3) : symMat (c • x) = c • symMat x := by
  ext i j; simp [symMat]

@[expose] def tauL (M : Matrix (Fin 4) (Fin 4) (ZMod 3)) : X3 →ₗ[ZMod 3] X3 where
  toFun x := fun k => (Mᵀ * symMat x * M) (pr k).1 (pr k).2
  map_add' x y := by
    ext k
    simp [symMat_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' c x := by
    ext k
    simp [symMat_smul]

theorem symMat_tauL (M : Matrix (Fin 4) (Fin 4) (ZMod 3)) (x : X3) :
    symMat (tauL M x) = Mᵀ * symMat x * M := by
  have hsym : (Mᵀ * symMat x * M)ᵀ = Mᵀ * symMat x * M := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, symMat_transpose, transpose_transpose,
      Matrix.mul_assoc]
  ext i j
  have h0 : symMat (tauL M x) i j =
      (Mᵀ * symMat x * M) (pr (cidx i j)).1 (pr (cidx i j)).2 := rfl
  rw [h0]
  rcases cidx_pr i j with h | h
  · rw [h]
  · rw [h]
    exact congrFun (congrFun hsym i) j

@[expose] def formL (B : Matrix (Fin 4) (Fin 4) (ZMod 3)) : X3 →ₗ[ZMod 3] ZMod 3 where
  toFun x := (B * symMat x).trace
  map_add' x y := by simp [symMat_add, Matrix.mul_add, Matrix.trace_add]
  map_smul' c x := by simp [symMat_smul]

theorem sum_single (x : X3) : x = ∑ k, x k • (Pi.single k (1 : ZMod 3) : X3) := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem linear_eq_sum (f : X3 →ₗ[ZMod 3] ZMod 3) (x : X3) :
    f x = ∑ k, x k * f (Pi.single k 1) := by
  conv_lhs => rw [sum_single x]
  simp [map_sum, map_smul]

theorem formL_single {B : Matrix (Fin 4) (Fin 4) (ZMod 3)} (hB : Bᵀ = B) (k : Fin 10) :
    formL B (Pi.single k 1) =
      B (pr k).1 (pr k).2 * (if (pr k).1 = (pr k).2 then 1 else 2) := by
  have h : ∀ i j, B j i = B i j := fun i j => by
    have := congrFun (congrFun hB i) j
    simpa [Matrix.transpose_apply] using this
  have h10 := h 0 1
  have h20 := h 0 2
  have h30 := h 0 3
  have h21 := h 1 2
  have h31 := h 1 3
  have h32 := h 2 3
  show (B * symMat (Pi.single k 1)).trace = _
  fin_cases k <;>
    simp [symMat, cidx, pr, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_four, Pi.single_apply,
      h10, h20, h30, h21, h31, h32] <;> ring

theorem exists_form (l : X3 →+ ZMod 3) :
    ∃ B : Matrix (Fin 4) (Fin 4) (ZMod 3), Bᵀ = B ∧ ∀ x, l x = formL B x := by
  let B : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
    Matrix.of fun i j => l (Pi.single (cidx i j) 1) * (if i = j then 1 else 2)
  have hB : Bᵀ = B := by
    ext i j
    simp [B, cidx_comm i j, eq_comm]
  refine ⟨B, hB, fun x => ?_⟩
  let lL : X3 →ₗ[ZMod 3] ZMod 3 :=
    { toFun := l
      map_add' := l.map_add
      map_smul' := fun c y => by
        have h : c • y = c.val • y := by
          rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [h, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val] }
  rw [show l x = lL x from rfl, linear_eq_sum lL x, linear_eq_sum (formL B) x]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  show l (Pi.single k 1) = _
  rw [formL_single hB k]
  have hk : cidx (pr k).1 (pr k).2 = k := by revert k; decide
  simp only [B, Matrix.of_apply, hk]
  by_cases h : (pr k).1 = (pr k).2
  · simp [h]
  · have h4 : (2 : ZMod 3) * 2 = 1 := by decide
    simp [h, mul_assoc, h4]

theorem form_inj {B B' : Matrix (Fin 4) (Fin 4) (ZMod 3)} (hB : Bᵀ = B) (hB' : B'ᵀ = B')
    (h : ∀ x, formL B x = formL B' x) : B = B' := by
  have hs : ∀ (M : Matrix (Fin 4) (Fin 4) (ZMod 3)), Mᵀ = M → ∀ i j, M j i = M i j := fun M hM i j => by
    have := congrFun (congrFun hM i) j
    simpa [Matrix.transpose_apply] using this
  ext i j
  have hk := h (Pi.single (cidx i j) 1)
  rw [formL_single hB, formL_single hB'] at hk
  have hc : (if (pr (cidx i j)).1 = (pr (cidx i j)).2 then (1 : ZMod 3) else 2) ≠ 0 := by
    split_ifs <;> decide
  have hcc := mul_right_cancel₀ hc hk
  rcases cidx_pr i j with h1 | h1
  · rw [h1] at hcc; exact hcc
  · rw [h1] at hcc
    simp only at hcc
    rw [hs B hB i j, hs B' hB' i j] at hcc
    exact hcc

theorem formL_tauL (B M : Matrix (Fin 4) (Fin 4) (ZMod 3)) (x : X3) :
    formL B (tauL M x) = formL (M * B * Mᵀ) x := by
  show (B * symMat (tauL M x)).trace = ((M * B * Mᵀ) * symMat x).trace
  rw [symMat_tauL]
  calc (B * (Mᵀ * symMat x * M)).trace = (M * (B * (Mᵀ * symMat x))).trace := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
        rw [Matrix.trace_mul_comm]
        simp [Matrix.mul_assoc]
    _ = _ := by simp [Matrix.mul_assoc]

theorem exists_diag_field {F : Type} [Field F] [Invertible (2 : F)] (B : Matrix (Fin 4) (Fin 4) F)
    (hB : Bᵀ = B) :
    ∃ C : Matrix (Fin 4) (Fin 4) F, C.det ≠ 0 ∧ ∀ i j, i ≠ j → (C * B * Cᵀ) i j = 0 := by
  have hsymm : (Matrix.toBilin' B).IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.2 hB
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.1 hsymm)
  have hfin : Module.finrank F (Fin 4 → F) = 4 := by simp
  let b' : Module.Basis (Fin 4) F (Fin 4 → F) := b.reindex (finCongr hfin)
  have hb' : ∀ i j, i ≠ j → Matrix.toBilin' B (b' i) (b' j) = 0 := by
    intro i j hij
    have hne : (finCongr hfin).symm i ≠ (finCongr hfin).symm j := fun h =>
      hij ((finCongr hfin).symm.injective h)
    have := hb hne
    simpa [b', Module.Basis.reindex_apply] using this
  let P : Matrix (Fin 4) (Fin 4) F := (Pi.basisFun F (Fin 4)).toMatrix b'
  have hP : P.det ≠ 0 := by
    have : IsUnit P.det := by
      have := (Pi.basisFun F (Fin 4)).invertibleToMatrix b'
      exact Matrix.isUnit_det_of_invertible P
    exact this.ne_zero
  refine ⟨Pᵀ, by simpa using hP, fun i j hij => ?_⟩
  have h := hb' i j hij
  rw [Matrix.toBilin'_apply'] at h
  have hPij : ∀ a c, P a c = b' c a := fun a c => by
    simp [P, Module.Basis.toMatrix_apply]
  have e : (Pᵀ * B * Pᵀᵀ) i j = (b' i) ⬝ᵥ (B *ᵥ (b' j)) := by
    simp only [transpose_transpose, Matrix.mul_apply, Matrix.mulVec, dotProduct, transpose_apply,
      hPij, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e]
  exact h

theorem exists_diag (B : Matrix (Fin 4) (Fin 4) (ZMod 3)) (hB : Bᵀ = B) :
    ∃ C : Matrix (Fin 4) (Fin 4) (ZMod 3), C.det ≠ 0 ∧
      ∀ i j, i ≠ j → (C * B * Cᵀ) i j = 0 := by
  have : Invertible (2 : ZMod 3) := ⟨2, by decide, by decide⟩
  exact exists_diag_field B hB

theorem formL_smul (c : ZMod 3) (B : Matrix (Fin 4) (Fin 4) (ZMod 3)) (x : X3) :
    formL (c • B) x = c * formL B x := by
  show ((c • B) * symMat x).trace = c * (B * symMat x).trace
  simp [Matrix.trace_smul]

theorem formL_zero (x : X3) : formL 0 x = 0 := by
  show ((0 : Matrix (Fin 4) (Fin 4) (ZMod 3)) * symMat x).trace = 0
  simp

open Classical in
theorem kernels_ge (A : Fin 29 → Matrix (Fin 4) (Fin 4) (ZMod 3))
    (hpd : ∀ a b c d : ZMod 3, ¬ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) →
      ∀ i j : Fin 29, i ≠ j → ∀ k : ZMod 3,
        A j * Matrix.diagonal ![a, b, c, d] * (A j)ᵀ ≠
          k • (A i * Matrix.diagonal ![a, b, c, d] * (A i)ᵀ))
    (hfz : ∀ a b c d : ZMod 3, ¬ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) →
      ∀ i : Fin 29, A i * Matrix.diagonal ![a, b, c, d] * (A i)ᵀ ≠ 0)
    (l : X3 →+ ZMod 3) (hl : l ≠ 0) :
    ∃ C : Matrix (Fin 4) (Fin 4) (ZMod 3), C.det ≠ 0 ∧
      29 ≤ ((Finset.univ : Finset (Fin 29)).image fun i =>
        (l.comp (tauL (A i * C)).toAddMonoidHom).ker).card := by
  obtain ⟨B, hBs, hlB⟩ := exists_form l
  obtain ⟨C, hCdet, hCd⟩ := exists_diag B hBs
  refine ⟨C, hCdet, ?_⟩
  have hB0 : B ≠ 0 := by
    rintro rfl
    apply hl
    refine AddMonoidHom.ext fun x => ?_
    rw [hlB x, formL_zero]
    rfl
  have hCu : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).2 (isUnit_iff_ne_zero.2 hCdet)
  have hCTu : IsUnit Cᵀ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
    exact isUnit_iff_ne_zero.2 hCdet
  have hDne : C * B * Cᵀ ≠ 0 := by
    intro h
    apply hB0
    rw [hCTu.mul_left_eq_zero, hCu.mul_right_eq_zero] at h
    exact h
  have hDdiag : C * B * Cᵀ = Matrix.diagonal ![(C * B * Cᵀ) 0 0, (C * B * Cᵀ) 1 1,
      (C * B * Cᵀ) 2 2, (C * B * Cᵀ) 3 3] := by
    ext i j
    by_cases hij : i = j
    · subst hij
      fin_cases i <;> simp
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact hCd i j hij
  obtain ⟨a, b, c, e, hDd⟩ : ∃ a b c e : ZMod 3, C * B * Cᵀ = Matrix.diagonal ![a, b, c, e] :=
    ⟨_, _, _, _, hDdiag⟩
  have hnz : ¬ (a = 0 ∧ b = 0 ∧ c = 0 ∧ e = 0) := by
    rintro ⟨rfl, rfl, rfl, rfl⟩
    apply hDne
    rw [hDd]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hkey : ∀ i x, l (tauL (A i * C) x) =
      formL (A i * Matrix.diagonal ![a, b, c, e] * (A i)ᵀ) x := by
    intro i x
    have hmm : (A i * C) * B * (A i * C)ᵀ = A i * (C * B * Cᵀ) * (A i)ᵀ := by
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [hlB, formL_tauL, hmm, hDd]
  have hFs : ∀ i, (A i * Matrix.diagonal ![a, b, c, e] * (A i)ᵀ)ᵀ =
      A i * Matrix.diagonal ![a, b, c, e] * (A i)ᵀ := by
    intro i
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have hinj : Function.Injective fun i : Fin 29 =>
      (l.comp (tauL (A i * C)).toAddMonoidHom).ker := by
    intro i j hij
    by_contra hne
    have hli : l.comp (tauL (A i * C)).toAddMonoidHom ≠ 0 := by
      intro h0
      apply hfz a b c e hnz i
      refine form_inj (hFs i) (by simp) fun x => ?_
      rw [← hkey i x, formL_zero]
      exact congrFun (congrArg DFunLike.coe h0) x
    have hker : ∀ x, (l.comp (tauL (A i * C)).toAddMonoidHom) x = 0 ↔
        (l.comp (tauL (A j * C)).toAddMonoidHom) x = 0 := by
      intro x
      have := SetLike.ext_iff.1 hij x
      simpa [AddMonoidHom.mem_ker] using this
    obtain ⟨k, hk⟩ := exists_smul_of_ker_eq_addHom _ _ hli hker
    have hFj : A j * Matrix.diagonal ![a, b, c, e] * (A j)ᵀ =
        k • (A i * Matrix.diagonal ![a, b, c, e] * (A i)ᵀ) := by
      refine form_inj (hFs j) (by rw [Matrix.transpose_smul, hFs i]) fun x => ?_
      rw [← hkey j x, formL_smul, ← hkey i x]
      exact hk x
    exact hpd a b c e hnz i j hne k hFj
  rw [Finset.card_image_of_injective _ hinj]
  simp

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
