module

public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquareLinear

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace CLSFourGroupScalarSquare

open Matrix FourGroupOddBilinear FourGroupOddUnitary QuaternionMatrices Module

section QuatBlock

variable {F : Type*} [Field F] {m : ℕ}

@[expose] def quatBlock (M : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F :=
  fromBlocks (M 0 0 • 1) (M 0 1 • 1) (M 1 0 • 1) (M 1 1 • 1)

theorem quatBlock_mul (M N : Matrix (Fin 2) (Fin 2) F) :
    quatBlock (m := m) M * quatBlock N = quatBlock (M * N) := by
  simp only [quatBlock, fromBlocks_multiply, smul_mul_smul_comm, Matrix.one_mul, ← add_smul,
    Matrix.mul_apply, Fin.sum_univ_two]

theorem quatBlock_one : quatBlock (m := m) (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  simp [quatBlock, fromBlocks_one]

theorem quatBlock_smul (c : F) (M : Matrix (Fin 2) (Fin 2) F) :
    quatBlock (m := m) (c • M) = c • quatBlock M := by
  simp [quatBlock, fromBlocks_smul, smul_smul]

theorem quatBlock_J (M : Matrix (Fin 2) (Fin 2) F) :
    (quatBlock (m := m) M)ᵀ * J (Fin m) F * quatBlock M = M.det • J (Fin m) F := by
  ext (i | i) (j | j) <;>
    simp [quatBlock, J, Matrix.mul_apply, Matrix.one_apply, det_fin_two,
      Fintype.sum_sum_type] <;> split_ifs <;> ring

theorem eq_of_quatBlock_eq_smul (hm : 0 < m) {M : Matrix (Fin 2) (Fin 2) F} {c : F}
    (h : quatBlock (m := m) M = c • 1) : M = c • 1 := by
  have k : Fin m := ⟨0, hm⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [quatBlock] using congrFun (congrFun h (Sum.inl k)) (Sum.inl k)
  · simpa [quatBlock] using congrFun (congrFun h (Sum.inl k)) (Sum.inr k)
  · simpa [quatBlock] using congrFun (congrFun h (Sum.inr k)) (Sum.inl k)
  · simpa [quatBlock] using congrFun (congrFun h (Sum.inr k)) (Sum.inr k)

end QuatBlock

section Units

variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module F W] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

@[expose] def basisGL (c : Basis ι F W) : GL ι F →* LinearMap.GeneralLinearGroup F W :=
  Units.map (Matrix.toLinAlgEquiv c : Matrix ι ι F →* Module.End F W)

theorem coe_basisGL (c : Basis ι F W) (M : GL ι F) :
    ((basisGL c M : LinearMap.GeneralLinearGroup F W) : Module.End F W) =
      Matrix.toLin c c (M : Matrix ι ι F) :=
  rfl

theorem toLin_preserves {σ : F →+* F} (h : W →ₛₗ[σ] W →ₗ[F] F) (c : Basis ι F W)
    (G : Matrix ι ι F) (hG : ∀ i j, h (c i) (c j) = G i j) {X : Matrix ι ι F}
    (hXσ : ∀ i j, σ (X i j) = X i j) (hXG : Xᵀ * G * X = G) (v w : W) :
    h (Matrix.toLin c c X v) (Matrix.toLin c c X w) = h v w := by
  have hext : (h.comp (Matrix.toLin c c X)).compl₂ (Matrix.toLin c c X) = h := by
    refine LinearMap.ext_basis c c fun i j => ?_
    rw [LinearMap.compl₂_apply, LinearMap.comp_apply, sesq_toLin_basis c G hG, hG,
      ← congrFun (congrFun hXG i) j]
    simp only [Matrix.mul_apply, transpose_apply, Finset.sum_mul, hXσ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  exact LinearMap.congr_fun₂ hext v w

@[expose] def involGL (X : Matrix ι ι F) (hX : X * X = 1) : GL ι F :=
  ⟨X, X, hX, hX⟩

theorem coe_involGL (X : Matrix ι ι F) (hX : X * X = 1) :
    (involGL X hX : Matrix ι ι F) = X :=
  rfl

theorem basisGL_neg (c : Basis ι F W) (M : GL ι F) : basisGL c (-M) = -basisGL c M := by
  refine Units.ext ?_
  rw [Units.val_neg, coe_basisGL, coe_basisGL, Units.val_neg, map_neg]

theorem coe_basisGL_ne_smul (c : Basis ι F W) {M : GL ι F}
    (hM : ∀ a : F, (M : Matrix ι ι F) ≠ a • 1) (a : F) :
    ((basisGL c M : LinearMap.GeneralLinearGroup F W) : Module.End F W) ≠ a • 1 := fun h =>
  hM a (toLin_eq_smul_id c (by rw [← coe_basisGL, h]; rfl))

end Units

section Quaternion

variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module F W]

@[expose] def quatHomEnd {m : ℕ} (c : Basis (Fin m ⊕ Fin m) F W) :
    Matrix (Fin 2) (Fin 2) F →* Module.End F W where
  toFun M := Matrix.toLin c c (quatBlock M)
  map_one' := by rw [quatBlock_one, Matrix.toLin_one]; rfl
  map_mul' M N := by rw [← quatBlock_mul, Matrix.toLin_mul c c c]; rfl

theorem exists_quat_sp [Finite F] (hF : ringChar F ≠ 2) [FiniteDimensional F W] [Nontrivial W]
    (B : LinearMap.BilinForm F W) (hB : B.IsAlt) (hnd : B.Nondegenerate) :
    ∃ i j : LinearMap.GeneralLinearGroup F W, i ∈ sesqUnitaryGroup B ∧ j ∈ sesqUnitaryGroup B ∧
      i * i = -1 ∧ j * j = -1 ∧ i * j = -(j * i) ∧
      (∀ a : F, (i : Module.End F W) ≠ a • 1) ∧ (∀ a : F, (j : Module.End F W) ≠ a • 1) ∧
      (∀ a : F, ((i * j : LinearMap.GeneralLinearGroup F W) : Module.End F W) ≠ a • 1) := by
  obtain ⟨m, c, hdim, hc⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_symplectic_basis B hB hnd
  have hm : 0 < m := by
    have := Module.finrank_pos (R := F) (M := W)
    omega
  obtain ⟨⟨a, b, hab⟩, -⟩ := odd_field_two_dimensional_quaternion_matrices hF
  have hG : ∀ k l, B (c k) (c l) = J (Fin m) F k l := fun k l => by
    rw [← hc, LinearMap.BilinForm.toMatrix_apply]
  let q := Units.map (quatHomEnd c)
  have hq : ∀ M : GL (Fin 2) F, ((q M : LinearMap.GeneralLinearGroup F W) : Module.End F W) =
      Matrix.toLin c c (quatBlock (M : Matrix (Fin 2) (Fin 2) F)) := fun _ => rfl
  let I := SpecialLinearGroup.toGL (slQuatI F)
  let J' := SpecialLinearGroup.toGL (slQuatJ hab)
  have hI : (I : Matrix (Fin 2) (Fin 2) F) = quatI F := rfl
  have hJ : (J' : Matrix (Fin 2) (Fin 2) F) = quatJ a b := rfl
  have hneg : q (-1) = -1 := by
    refine Units.ext ?_
    rw [hq, Units.val_neg, Units.val_one, Units.val_neg, Units.val_one,
      show (-1 : Matrix (Fin 2) (Fin 2) F) = (-1 : F) • 1 by rw [neg_one_smul], quatBlock_smul,
      quatBlock_one, map_smul, Matrix.toLin_one, neg_one_smul]
    rfl
  have hII : I * I = -1 := Units.ext (by rw [Units.val_mul, hI, quatI_mul_self]; rfl)
  have hJJ : J' * J' = -1 := Units.ext (by rw [Units.val_mul, hJ, quatJ_mul_self hab]; rfl)
  have hIJ : I * J' = -(J' * I) := Units.ext (by
    rw [Units.val_mul, Units.val_neg, Units.val_mul, hI, hJ, quatI_mul_quatJ_eq_neg])
  have hmem : ∀ M : SpecialLinearGroup (Fin 2) F,
      q (SpecialLinearGroup.toGL M) ∈ sesqUnitaryGroup B := fun M x y => by
    rw [hq]
    exact toLin_preserves B c (J (Fin m) F) hG (fun _ _ => rfl)
      (by rw [quatBlock_J]; change (M : Matrix (Fin 2) (Fin 2) F).det • _ = _
          rw [M.prop, one_smul]) x y
  have hns : ∀ M : Matrix (Fin 2) (Fin 2) F, (∀ r : F, M ≠ r • 1) → ∀ r : F,
      Matrix.toLin c c (quatBlock M) ≠ r • (1 : Module.End F W) := fun M hM r h =>
    hM r (eq_of_quatBlock_eq_smul hm (toLin_eq_smul_id c (by rw [h]; rfl)))
  have hIns : ∀ r : F, quatI F ≠ r • 1 := fun r h => by
    have := congrFun (congrFun h 0) 1
    simp [quatI] at this
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hJns : ∀ r : F, quatJ a b ≠ r • 1 := fun r h => by
    have h01 := congrFun (congrFun h 0) 1
    have h00 := congrFun (congrFun h 0) 0
    have h11 := congrFun (congrFun h 1) 1
    simp [quatJ] at h01 h00 h11
    have ha : a = 0 := by
      have h2a : (2 : F) * a = 0 := by linear_combination h00 - h11
      exact (mul_eq_zero.1 h2a).resolve_left h2
    rw [ha, h01] at hab
    norm_num at hab
  have hIJns : ∀ r : F, quatI F * quatJ a b ≠ r • 1 := fun r h => by
    rw [quatI_mul_quatJ] at h
    have h01 := congrFun (congrFun h 0) 1
    have h00 := congrFun (congrFun h 0) 0
    have h11 := congrFun (congrFun h 1) 1
    simp at h01 h00 h11
    have hb : b = 0 := by
      have h2b : (2 : F) * b = 0 := by linear_combination h00 - h11
      exact (mul_eq_zero.1 h2b).resolve_left h2
    rw [hb, h01] at hab
    norm_num at hab
  refine ⟨q I, q J', hmem _, hmem _, by rw [← map_mul, hII, hneg], by rw [← map_mul, hJJ, hneg],
    by rw [← map_mul, hIJ, ← neg_one_mul, map_mul, hneg, map_mul, neg_one_mul],
    by rw [hq, hI]; exact hns _ hIns, by rw [hq, hJ]; exact hns _ hJns, ?_⟩
  rw [← map_mul, hq, Units.val_mul, hI, hJ]
  exact hns _ hIJns

end Quaternion

section SignSwap

variable {F : Type*} [Field F]

@[expose] def swapMat : Matrix (Fin 2) (Fin 2) F :=
  !![0, 1; 1, 0]

theorem exists_sign_swap (h2 : (2 : F) ≠ 0) {r : ℕ} (hr : 2 ≤ r) :
    ∃ X Y : Matrix (Fin r) (Fin r) F, X * X = 1 ∧ Y * Y = 1 ∧
      (X * Y = Y * X ∨ X * Y = -(Y * X)) ∧ (∀ a : F, X ≠ a • 1) ∧ (∀ a : F, Y ≠ a • 1) ∧
      (∀ a : F, X * Y ≠ a • 1) ∧ Xᵀ * X = 1 ∧ Yᵀ * Y = 1 ∧
      (∀ σ : F →+* F, ∀ i j, σ (X i j) = X i j) ∧ (∀ σ : F →+* F, ∀ i j, σ (Y i j) = Y i j) := by
  have hσ : ∀ (σ : F →+* F) (S : Finset (Fin r)) (i j : Fin r),
      σ (signDiag S i j) = signDiag S i j := fun σ S i j => map_signDiag σ S i j
  rcases Nat.lt_or_ge r 3 with h3 | h3
  · have hr2 : r = 2 := by omega
    subst hr2
    refine ⟨!![-1, 0; 0, 1], swapMat, ?_, ?_, Or.inr ?_, fun a h => ?_, fun a h => ?_,
      fun a h => ?_, ?_, ?_, fun σ i j => ?_, fun σ i j => ?_⟩
    · rw [Matrix.mul_fin_two, Matrix.one_fin_two]
      norm_num
    · rw [swapMat, Matrix.mul_fin_two, Matrix.one_fin_two]
      norm_num
    · rw [swapMat, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.neg_of]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · have h00 := congrFun (congrFun h 0) 0
      have h11 := congrFun (congrFun h 1) 1
      simp at h00 h11
      exact h2 (by linear_combination h11 - h00)
    · have := congrFun (congrFun h 0) 1
      simp [swapMat] at this
    · rw [swapMat, Matrix.mul_fin_two] at h
      have := congrFun (congrFun h 0) 1
      simp at this
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [swapMat, Matrix.mul_apply, Fin.sum_univ_two]
    · fin_cases i <;> fin_cases j <;> simp
    · fin_cases i <;> fin_cases j <;> simp [swapMat]
  · let i₀ : Fin r := ⟨0, by omega⟩
    let i₁ : Fin r := ⟨1, by omega⟩
    let i₂ : Fin r := ⟨2, by omega⟩
    have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
    have h02 : i₀ ≠ i₂ := by simp [i₀, i₂, Fin.ext_iff]
    have h12 : i₁ ≠ i₂ := by simp [i₁, i₂, Fin.ext_iff]
    refine ⟨signDiag {i₀}, signDiag {i₁}, signDiag_mul_self _, signDiag_mul_self _,
      Or.inl (signDiag_comm _ _),
      signDiag_ne_smul h2 (i := i₀) (j := i₁) (by simp) (by simp [h01.symm]),
      signDiag_ne_smul h2 (i := i₁) (j := i₀) (by simp) (by simp [h01]), fun a => ?_,
      by rw [transpose_signDiag, signDiag_mul_self], by rw [transpose_signDiag, signDiag_mul_self],
      fun σ i j => hσ σ _ i j, fun σ i j => hσ σ _ i j⟩
    rw [signDiag_mul_signDiag]
    exact signDiag_ne_smul h2 (i := i₀) (j := i₂) (by simp [Finset.mem_symmDiff, h01])
      (by simp [Finset.mem_symmDiff, h02.symm, h12.symm]) a

end SignSwap

section Restrict

variable {K E : Type*} [Field K] [Field E] [Algebra K E] {V : Type*} [AddCommGroup V] [Module K V]
  [Module E V] [IsScalarTower K E V]

@[expose] def restrictGL : LinearMap.GeneralLinearGroup E V →* LinearMap.GeneralLinearGroup K V :=
  Units.map
    { toFun := LinearMap.restrictScalars K
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem coe_restrictGL (g : LinearMap.GeneralLinearGroup E V) :
    ((restrictGL g : LinearMap.GeneralLinearGroup K V) : Module.End K V) =
      (g : Module.End E V).restrictScalars K :=
  rfl

theorem restrictGL_apply (g : LinearMap.GeneralLinearGroup E V) (v : V) :
    ((restrictGL g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v =
      (g : Module.End E V) v :=
  rfl

theorem restrictGL_neg (g : LinearMap.GeneralLinearGroup E V) :
    restrictGL (K := K) (-g) = -restrictGL g :=
  Units.ext rfl

theorem coe_restrictGL_ne_smul {g : LinearMap.GeneralLinearGroup E V}
    (hg : ∀ a : E, (g : Module.End E V) ≠ a • 1) (a : K) :
    ((restrictGL g : LinearMap.GeneralLinearGroup K V) : Module.End K V) ≠ a • 1 := fun h => by
  refine hg (algebraMap K E a) (LinearMap.ext fun v => ?_)
  have := congrArg (fun φ : Module.End K V => φ v) h
  simp only [restrictGL_apply, LinearMap.smul_apply, Module.End.one_apply] at this
  rw [this, LinearMap.smul_apply, Module.End.one_apply, algebraMap_smul]

end Restrict

end CLSFourGroupScalarSquare

end CFSG.LocalAnalysis.ComponentInitial
