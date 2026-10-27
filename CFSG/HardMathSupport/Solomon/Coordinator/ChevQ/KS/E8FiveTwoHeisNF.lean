module

public import CFSG.LieType.SeitzGeneration.InnerThreeUnitaryLeaves

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five

namespace Two

open Matrix

section HeisNF

variable {L : Type} [Field L]

@[expose] def shiftMat (c : L) : Matrix (Fin 5) (Fin 5) L :=
  Matrix.of fun i j => if i = j + 1 then (if j = 4 then c else 1) else 0

theorem shiftMat_eq_perm (c : L) :
    shiftMat c = ((finRotate 5)⁻¹).permMatrix L *
      Matrix.diagonal (fun j : Fin 5 => if j = 4 then c else 1) := by
  ext i j
  rw [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    simp [shiftMat, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.Perm.inv_def,
      show (-1 : Fin 5) = 4 by decide]
theorem shiftMat_det (c : L) : (shiftMat c).det = c := by
  rw [shiftMat_eq_perm, Matrix.det_mul, Matrix.det_permutation, Matrix.det_diagonal,
    Equiv.Perm.sign_inv, sign_finRotate, Fin.prod_univ_five]
  norm_num

theorem heis_normal_form [IsAlgClosed L] {κ : L} (hκ : IsPrimitiveRoot κ 5)
    {M₀ M₁ : Matrix (Fin 5) (Fin 5) L} (h₀ : IsUnit M₀) (h₁ : IsUnit M₁)
    (hc : M₀ * M₁ = κ • (M₁ * M₀)) {c : L} (h5 : M₁ ^ 5 = c • 1) :
    ∃ (S : GL (Fin 5) L) (ν : L), ν ≠ 0 ∧
      M₀ * (S : Matrix (Fin 5) (Fin 5) L) =
        (S : Matrix (Fin 5) (Fin 5) L) * diagonal (fun i : Fin 5 => ν * κ ^ (i : ℕ)) ∧
      M₁ * (S : Matrix (Fin 5) (Fin 5) L) = (S : Matrix (Fin 5) (Fin 5) L) * shiftMat c := by
  classical
  obtain ⟨ν, hν⟩ := Module.End.exists_eigenvalue (Matrix.toLin' M₀)
  obtain ⟨v, hv⟩ := hν.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hMv : M₀.mulVec v = ν • v := by
    have := hv.apply_eq_smul
    simpa using this
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hMv
    have : v = 0 := by
      have h2 := congrArg (fun w => (M₀⁻¹).mulVec w) hMv
      simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 h₀)]
        using h2
    exact hv0 this
  set w : Fin 5 → (Fin 5 → L) := fun k => (M₁ ^ (k : ℕ)).mulVec v with hw
  have hw_eig : ∀ k : Fin 5, M₀.mulVec (w k) = (ν * κ ^ (k : ℕ)) • w k := by
    intro k
    simp only [hw]
    rw [Matrix.mulVec_mulVec, CFSG.LieType.SeitzGeneration.mat_mul_pow_eq_smul hc,
      Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
      hMv, Matrix.mulVec_smul, smul_smul, mul_comm]
  have hw_ne : ∀ k : Fin 5, w k ≠ 0 := by
    intro k hk
    apply hv0
    have hu : IsUnit (M₁ ^ (k : ℕ)) := h₁.pow _
    have h2 := congrArg (fun u => ((M₁ ^ (k : ℕ))⁻¹).mulVec u) hk
    simpa [hw, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)] using h2
  have hinj : Function.Injective fun k : Fin 5 => ν * κ ^ (k : ℕ) := by
    intro i j hij
    have h1 : κ ^ (i : ℕ) = κ ^ (j : ℕ) := mul_left_cancel₀ hν0 hij
    exact Fin.ext (hκ.pow_inj i.isLt j.isLt h1)
  have hli : LinearIndependent L w := by
    refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' M₀)
      (fun k : Fin 5 => ν * κ ^ (k : ℕ)) hinj w fun k => ?_
    refine ⟨Module.End.mem_eigenspace_iff.2 ?_, hw_ne k⟩
    simpa using hw_eig k
  set S0 : Matrix (Fin 5) (Fin 5) L := Matrix.of fun r k => w k r with hS0
  have hS0u : IsUnit S0 := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli
  have hS0c : ∀ r k, S0 r k = w k r := fun r k => rfl
  refine ⟨hS0u.unit, ν, hν0, ?_, ?_⟩
  · rw [IsUnit.unit_spec]
    ext r k
    have h1 : (M₀ * S0) r k = (M₀.mulVec (w k)) r := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hS0c]
    rw [h1, hw_eig k]
    simp [Matrix.mul_apply, Matrix.diagonal_apply, hS0c, mul_comm]
  · rw [IsUnit.unit_spec]
    have hstep : ∀ k : Fin 5, M₁.mulVec (w k) = (if k = 4 then c else 1) • w (k + 1) := by
      intro k
      by_cases hk : k = 4
      · subst hk
        simp only [hw, Matrix.mulVec_mulVec, if_true]
        rw [← pow_succ']
        show (M₁ ^ 5).mulVec v = c • (M₁ ^ 0).mulVec v
        rw [h5, Matrix.smul_mulVec, Matrix.one_mulVec, pow_zero, Matrix.one_mulVec]
      · have hk4 : (k : ℕ) < 4 := by
          have := k.isLt
          have h2 : (k : ℕ) ≠ 4 := fun h => hk (Fin.ext h)
          omega
        simp only [hw, Matrix.mulVec_mulVec, hk, if_false, one_smul]
        rw [← pow_succ']
        congr 2
        rw [Fin.val_add_one_of_lt (by simpa [Fin.lt_def] using hk4)]
    ext r k
    have h1 : (M₁ * S0) r k = (M₁.mulVec (w k)) r := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hS0c]
    rw [h1, hstep k]
    simp [Matrix.mul_apply, shiftMat, hS0c, Finset.sum_ite_eq]
    by_cases hk : k = 4 <;> simp [hk, mul_comm]

theorem heis_schur [IsAlgClosed L] {κ : L} (hκ : IsPrimitiveRoot κ 5)
    {M₀ M₁ : Matrix (Fin 5) (Fin 5) L} (h₀ : IsUnit M₀) (h₁ : IsUnit M₁)
    (hc : M₀ * M₁ = κ • (M₁ * M₀)) {c : L} (h5 : M₁ ^ 5 = c • 1)
    {N : Matrix (Fin 5) (Fin 5) L} (hN₀ : N * M₀ = M₀ * N) (hN₁ : N * M₁ = M₁ * N) :
    ∃ n : L, N = n • 1 := by
  classical
  obtain ⟨S, ν, hν, hD, hQ⟩ := heis_normal_form hκ h₀ h₁ hc h5
  set Sm : Matrix (Fin 5) (Fin 5) L := (S : Matrix (Fin 5) (Fin 5) L) with hSm
  set Si : Matrix (Fin 5) (Fin 5) L := ((S⁻¹ : GL (Fin 5) L) : Matrix (Fin 5) (Fin 5) L) with hSi
  have hSiS : Si * Sm = 1 := S.inv_mul
  have hSSi : Sm * Si = 1 := S.mul_inv
  set N' : Matrix (Fin 5) (Fin 5) L := Si * N * Sm with hN'
  set D : Matrix (Fin 5) (Fin 5) L := diagonal (fun i : Fin 5 => ν * κ ^ (i : ℕ)) with hDdef
  have hSiM₀ : Si * M₀ = D * Si := by
    calc Si * M₀ = Si * M₀ * (Sm * Si) := by rw [hSSi, Matrix.mul_one]
      _ = Si * (M₀ * Sm) * Si := by simp only [Matrix.mul_assoc]
      _ = Si * (Sm * D) * Si := by rw [hD]
      _ = D * Si := by simp only [← Matrix.mul_assoc, hSiS, Matrix.one_mul]
  have hSiM₁ : Si * M₁ = shiftMat c * Si := by
    calc Si * M₁ = Si * M₁ * (Sm * Si) := by rw [hSSi, Matrix.mul_one]
      _ = Si * (M₁ * Sm) * Si := by simp only [Matrix.mul_assoc]
      _ = Si * (Sm * shiftMat c) * Si := by rw [hQ]
      _ = shiftMat c * Si := by simp only [← Matrix.mul_assoc, hSiS, Matrix.one_mul]
  have hND : N' * D = D * N' := by
    calc N' * D = Si * N * (Sm * D) := by simp only [hN', Matrix.mul_assoc]
      _ = Si * N * (M₀ * Sm) := by rw [← hD]
      _ = Si * (N * M₀) * Sm := by simp only [Matrix.mul_assoc]
      _ = Si * (M₀ * N) * Sm := by rw [hN₀]
      _ = (Si * M₀) * N * Sm := by simp only [Matrix.mul_assoc]
      _ = (D * Si) * N * Sm := by rw [hSiM₀]
      _ = D * N' := by simp only [hN', Matrix.mul_assoc]
  have hNQ : N' * shiftMat c = shiftMat c * N' := by
    calc N' * shiftMat c = Si * N * (Sm * shiftMat c) := by simp only [hN', Matrix.mul_assoc]
      _ = Si * N * (M₁ * Sm) := by rw [← hQ]
      _ = Si * (N * M₁) * Sm := by simp only [Matrix.mul_assoc]
      _ = Si * (M₁ * N) * Sm := by rw [hN₁]
      _ = (Si * M₁) * N * Sm := by simp only [Matrix.mul_assoc]
      _ = (shiftMat c * Si) * N * Sm := by rw [hSiM₁]
      _ = shiftMat c * N' := by simp only [hN', Matrix.mul_assoc]
  have hdiag : ∀ i j : Fin 5, i ≠ j → N' i j = 0 := by
    intro i j hij
    have h := congrFun (congrFun hND i) j
    simp only [Matrix.mul_apply, hDdef, Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero,
      zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    have h2 : (ν * κ ^ (j : ℕ) - ν * κ ^ (i : ℕ)) * N' i j = 0 := by linear_combination h
    have h3 : ν * κ ^ (j : ℕ) - ν * κ ^ (i : ℕ) ≠ 0 := by
      intro h4
      have h5' : κ ^ (j : ℕ) = κ ^ (i : ℕ) := mul_left_cancel₀ hν (sub_eq_zero.1 h4)
      exact hij (Fin.ext (hκ.pow_inj i.isLt j.isLt h5'.symm))
    exact (mul_eq_zero.1 h2).resolve_left h3
  have hstep : ∀ j : Fin 5, j ≠ 4 → N' (j + 1) (j + 1) = N' j j := by
    intro j hj
    have h := congrFun (congrFun hNQ (j + 1)) j
    simp only [Matrix.mul_apply, shiftMat, Matrix.of_apply, mul_ite, ite_mul, mul_zero,
      zero_mul, mul_one, one_mul, hj, if_false, add_left_inj, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    exact h
  have hall : ∀ i : Fin 5, N' i i = N' 0 0 := by
    intro i
    have h0 := hstep 0 (by decide)
    have h1 := hstep 1 (by decide)
    have h2 := hstep 2 (by decide)
    have h3 := hstep 3 (by decide)
    fin_cases i
    · rfl
    · simpa using h0
    · simpa using h1.trans h0
    · simpa using h2.trans (h1.trans h0)
    · simpa using h3.trans (h2.trans (h1.trans h0))
  refine ⟨N' 0 0, ?_⟩
  have hN'1 : N' = N' 0 0 • (1 : Matrix (Fin 5) (Fin 5) L) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hall i]
    · simp [hdiag i j hij, Matrix.one_apply_ne hij]
  have hN : N = Sm * N' * Si := by
    calc N = (Sm * Si) * N * (Sm * Si) := by rw [hSSi, Matrix.one_mul, Matrix.mul_one]
      _ = Sm * N' * Si := by simp only [hN', Matrix.mul_assoc]
  rw [hN, hN'1]
  simp [Matrix.mul_smul, Matrix.smul_mul, hSSi]

theorem exists_conj_diag_enum [IsAlgClosed L] {κ : L} (hκ : IsPrimitiveRoot κ 5)
    {M₀ M₁ : Matrix (Fin 5) (Fin 5) L} (h₀ : IsUnit M₀) (h₁ : IsUnit M₁)
    (hc : M₀ * M₁ = κ • (M₁ * M₀)) {c : L} (h5 : M₁ ^ 5 = c • 1) (hdet : M₀.det = 1)
    (d : Fin 5 → L) (hd : Function.Injective d) (hd5 : ∀ i, d i ^ 5 = 1) :
    ∃ S : GL (Fin 5) L, M₀ * (S : Matrix (Fin 5) (Fin 5) L) =
      (S : Matrix (Fin 5) (Fin 5) L) * diagonal d := by
  classical
  obtain ⟨S₀, ν, hν, hD, -⟩ := heis_normal_form hκ h₀ h₁ hc h5
  set Sm : Matrix (Fin 5) (Fin 5) L := (S₀ : Matrix (Fin 5) (Fin 5) L) with hSm
  have hSdet : IsUnit Sm.det := (Matrix.isUnit_iff_isUnit_det _).1 S₀.isUnit
  have hprod : ∏ i : Fin 5, (ν * κ ^ (i : ℕ)) = ν ^ 5 * κ ^ 10 := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.prod_pow_eq_pow_sum]
    congr 2
  have hν5 : ν ^ 5 = 1 := by
    have h1 := congrArg Matrix.det hD
    rw [Matrix.det_mul, Matrix.det_mul, hdet, one_mul, Matrix.det_diagonal, hprod] at h1
    have h2 : ν ^ 5 * κ ^ 10 = 1 := by
      have h3 : Sm.det * (ν ^ 5 * κ ^ 10) = Sm.det * 1 := by rw [mul_one]; exact h1.symm
      exact mul_left_cancel₀ hSdet.ne_zero h3
    have h4 : κ ^ 10 = 1 := by
      rw [show 10 = 5 * 2 by norm_num, pow_mul, hκ.pow_eq_one, one_pow]
    rwa [h4, mul_one] at h2
  have hex : ∀ i : Fin 5, ∃ k : Fin 5, ν * κ ^ (k : ℕ) = d i := by
    intro i
    have h1 : (d i / ν) ^ 5 = 1 := by rw [div_pow, hd5 i, hν5, div_one]
    obtain ⟨k, hk, hk'⟩ := hκ.eq_pow_of_pow_eq_one h1
    exact ⟨⟨k, hk⟩, by simp only [hk']; field_simp⟩
  choose π hπ using hex
  have hπinj : Function.Injective π := by
    intro i j hij
    apply hd
    rw [← hπ i, ← hπ j, hij]
  have hπbij : Function.Bijective π := Finite.injective_iff_bijective.1 hπinj
  set S' : Matrix (Fin 5) (Fin 5) L := Sm.submatrix id π with hS'
  have hli : LinearIndependent L (fun j => Sm.col j) :=
    Matrix.linearIndependent_cols_iff_isUnit.2 S₀.isUnit
  have hS'u : IsUnit S' := Matrix.linearIndependent_cols_iff_isUnit.1 (hli.comp π hπinj)
  refine ⟨hS'u.unit, ?_⟩
  rw [IsUnit.unit_spec]
  ext r i
  have h1 : (M₀ * S') r i = (M₀ * Sm) r (π i) := by
    simp [hS', Matrix.mul_apply]
  rw [h1, hD]
  simp [hS', Matrix.mul_apply, Matrix.diagonal_apply, ← hπ i]

open CFSG.LieType.SeitzGeneration
open scoped MatrixGroups

section AlgClosed

variable [IsAlgClosed L]

theorem heis_normal_form_sl {κ : L} (hκ : IsPrimitiveRoot κ 5)
    {M₀ M₁ : Matrix (Fin 5) (Fin 5) L} (h₀ : IsUnit M₀) (h₁ : IsUnit M₁)
    (hc : M₀ * M₁ = κ • (M₁ * M₀)) {c : L} (h5 : M₁ ^ 5 = c • 1)
    (hdet0 : M₀.det = 1) (hdet1 : M₁.det = 1) :
    c = 1 ∧ ∃ (S : GL (Fin 5) L) (ν : L), ν ≠ 0 ∧ ν ^ 5 = 1 ∧
      M₀ * (S : Matrix (Fin 5) (Fin 5) L) =
        (S : Matrix (Fin 5) (Fin 5) L) * diagonal (fun i : Fin 5 => ν * κ ^ (i : ℕ)) ∧
      M₁ * (S : Matrix (Fin 5) (Fin 5) L) = (S : Matrix (Fin 5) (Fin 5) L) * shiftMat 1 := by
  classical
  obtain ⟨S, ν, hν0, hD, hQ⟩ := heis_normal_form hκ h₀ h₁ hc h5
  set Sm : Matrix (Fin 5) (Fin 5) L := (S : Matrix (Fin 5) (Fin 5) L) with hSm
  have hSdet : IsUnit Sm.det := by
    simpa [hSm] using
      (Matrix.isUnit_iff_isUnit_det (S : Matrix (Fin 5) (Fin 5) L)).1 S.isUnit
  have hc1 : c = 1 := by
    have h1 := congrArg Matrix.det hQ
    rw [Matrix.det_mul, Matrix.det_mul, hdet1, one_mul, shiftMat_det] at h1
    have h2 : Sm.det * c = Sm.det * 1 := by
      rw [mul_one]
      exact h1.symm
    exact mul_left_cancel₀ hSdet.ne_zero h2
  have hν5 : ν ^ 5 = 1 := by
    have hprod : ∏ i : Fin 5, (ν * κ ^ (i : ℕ)) = ν ^ 5 * κ ^ 10 := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Finset.prod_pow_eq_pow_sum]
      congr 2
    have h1 := congrArg Matrix.det hD
    rw [Matrix.det_mul, Matrix.det_mul, hdet0, one_mul, Matrix.det_diagonal, hprod] at h1
    have h2 : ν ^ 5 * κ ^ 10 = 1 := by
      have h3 : Sm.det * (ν ^ 5 * κ ^ 10) = Sm.det * 1 := by
        rw [mul_one]
        exact h1.symm
      exact mul_left_cancel₀ hSdet.ne_zero h3
    have h4 : κ ^ 10 = 1 := by
      rw [show 10 = 5 * 2 by norm_num, pow_mul, hκ.pow_eq_one, one_pow]
    rwa [h4, mul_one] at h2
  refine ⟨hc1, S, ν, hν0, hν5, hD, ?_⟩
  simpa [hc1] using hQ

theorem heis_normal_form_clock_shift {κ : L} (hκ : IsPrimitiveRoot κ 5)
    {M₀ M₁ : Matrix (Fin 5) (Fin 5) L} (h₀ : IsUnit M₀) (h₁ : IsUnit M₁)
    (hc : M₀ * M₁ = κ • (M₁ * M₀)) {c : L} (h5 : M₁ ^ 5 = c • 1)
    (hdet0 : M₀.det = 1) (hdet1 : M₁.det = 1) :
    ∃ S : GL (Fin 5) L,
      M₀ * (S : Matrix (Fin 5) (Fin 5) L) =
        (S : Matrix (Fin 5) (Fin 5) L) * diagonal (fun i : Fin 5 => κ ^ (i : ℕ)) ∧
      M₁ * (S : Matrix (Fin 5) (Fin 5) L) =
        (S : Matrix (Fin 5) (Fin 5) L) * shiftMat 1 := by
  classical
  obtain ⟨-, S, ν, hν0, hν5, hD, hQ⟩ :=
    heis_normal_form_sl hκ h₀ h₁ hc h5 hdet0 hdet1
  obtain ⟨j, hjlt, hj⟩ := hκ.eq_pow_of_pow_eq_one hν5
  set Sm : Matrix (Fin 5) (Fin 5) L := (S : Matrix (Fin 5) (Fin 5) L) with hSm
  set Si : Matrix (Fin 5) (Fin 5) L := ((S⁻¹ : GL (Fin 5) L) :
    Matrix (Fin 5) (Fin 5) L) with hSi
  have hSiS : Si * Sm = 1 := S.inv_mul
  have hSSi : Sm * Si = 1 := S.mul_inv
  set Dν : Matrix (Fin 5) (Fin 5) L :=
    diagonal (fun i : Fin 5 => ν * κ ^ (i : ℕ)) with hDν
  set D1 : Matrix (Fin 5) (Fin 5) L :=
    diagonal (fun i : Fin 5 => κ ^ (i : ℕ)) with hD1
  set Q : Matrix (Fin 5) (Fin 5) L := shiftMat 1 with hQdef
  have hD' : M₀ * Sm = Sm * Dν := by simpa [← hDν] using hD
  have hQ' : M₁ * Sm = Sm * Q := by simpa [← hQdef] using hQ
  have hDQS : Sm * (Dν * Q) = Sm * (κ • (Q * Dν)) := by
    calc Sm * (Dν * Q) = (Sm * Dν) * Q := by rw [Matrix.mul_assoc]
      _ = (M₀ * Sm) * Q := by rw [← hD']
      _ = M₀ * (Sm * Q) := by rw [Matrix.mul_assoc]
      _ = M₀ * (M₁ * Sm) := by rw [← hQ']
      _ = (M₀ * M₁) * Sm := by rw [Matrix.mul_assoc]
      _ = (κ • (M₁ * M₀)) * Sm := by rw [hc]
      _ = κ • ((M₁ * M₀) * Sm) := by rw [Matrix.smul_mul]
      _ = κ • (M₁ * (M₀ * Sm)) := by rw [Matrix.mul_assoc]
      _ = κ • (M₁ * (Sm * Dν)) := by rw [hD']
      _ = κ • ((M₁ * Sm) * Dν) := by rw [Matrix.mul_assoc]
      _ = κ • ((Sm * Q) * Dν) := by rw [hQ']
      _ = κ • (Sm * (Q * Dν)) := by rw [Matrix.mul_assoc]
      _ = Sm * (κ • (Q * Dν)) := by rw [← Matrix.mul_smul]
  have hDQ : Dν * Q = κ • (Q * Dν) := by
    have h := congrArg (fun X => Si * X) hDQS
    simpa only [← Matrix.mul_assoc, hSiS, Matrix.one_mul] using h
  have hDν_smul : Dν = ν • D1 := by
    rw [hDν, hD1, ← Matrix.diagonal_smul]
    congr 1
  have hκpow : κ ^ (5 - j) * ν = 1 := by
    rw [← hj, ← pow_add, Nat.sub_add_cancel (Nat.le_of_lt hjlt), hκ.pow_eq_one]
  have hDshift : Dν * Q ^ (5 - j) = Q ^ (5 - j) * D1 := by
    have hstep := mat_mul_pow_eq_smul hDQ (5 - j)
    calc Dν * Q ^ (5 - j) = κ ^ (5 - j) • (Q ^ (5 - j) * Dν) := hstep
      _ = κ ^ (5 - j) • (Q ^ (5 - j) * (ν • D1)) := by rw [hDν_smul]
      _ = κ ^ (5 - j) • (ν • (Q ^ (5 - j) * D1)) := by rw [Matrix.mul_smul]
      _ = (κ ^ (5 - j) * ν) • (Q ^ (5 - j) * D1) := by rw [smul_smul]
      _ = Q ^ (5 - j) * D1 := by rw [hκpow, one_smul]
  have hQunit : IsUnit Q := by
    rw [hQdef]
    exact (Matrix.isUnit_iff_isUnit_det _).2 (by rw [shiftMat_det]; exact isUnit_one)
  let q : GL (Fin 5) L := hQunit.unit
  have hq : (q : Matrix (Fin 5) (Fin 5) L) = Q := IsUnit.unit_spec hQunit
  let U : GL (Fin 5) L := S * q ^ (5 - j)
  have hUcoe : (U : Matrix (Fin 5) (Fin 5) L) = Sm * Q ^ (5 - j) := by
    simp [U, hq, hSm, Units.val_pow_eq_pow_val]
  have hM0U : M₀ * (U : Matrix (Fin 5) (Fin 5) L) = (U : Matrix (Fin 5) (Fin 5) L) * D1 := by
    rw [hUcoe]
    calc M₀ * (Sm * Q ^ (5 - j)) = (M₀ * Sm) * Q ^ (5 - j) := by rw [Matrix.mul_assoc]
      _ = (Sm * Dν) * Q ^ (5 - j) := by rw [hD']
      _ = Sm * (Dν * Q ^ (5 - j)) := by rw [Matrix.mul_assoc]
      _ = Sm * (Q ^ (5 - j) * D1) := by rw [hDshift]
      _ = (Sm * Q ^ (5 - j)) * D1 := by rw [Matrix.mul_assoc]
  have hM1U : M₁ * (U : Matrix (Fin 5) (Fin 5) L) = (U : Matrix (Fin 5) (Fin 5) L) * Q := by
    rw [hUcoe]
    calc M₁ * (Sm * Q ^ (5 - j)) = (M₁ * Sm) * Q ^ (5 - j) := by rw [Matrix.mul_assoc]
      _ = (Sm * Q) * Q ^ (5 - j) := by rw [hQ']
      _ = Sm * (Q * Q ^ (5 - j)) := by rw [Matrix.mul_assoc]
      _ = Sm * Q ^ ((5 - j) + 1) := by rw [← pow_succ']
      _ = Sm * (Q ^ (5 - j) * Q) := by rw [pow_succ]
      _ = (Sm * Q ^ (5 - j)) * Q := by rw [Matrix.mul_assoc]
  refine ⟨U, ?_, ?_⟩
  · simpa [hD1] using hM0U
  · simpa [hQdef] using hM1U

theorem exists_conj_heis_pairs {κ : L} (hκ : IsPrimitiveRoot κ 5)
    {M₀ M₁ N₀ N₁ : Matrix (Fin 5) (Fin 5) L}
    (hM0 : IsUnit M₀) (hM1 : IsUnit M₁) (hN0 : IsUnit N₀) (hN1 : IsUnit N₁)
    (hcM : M₀ * M₁ = κ • (M₁ * M₀)) (hcN : N₀ * N₁ = κ • (N₁ * N₀))
    {c d : L} (h5M : M₁ ^ 5 = c • 1) (h5N : N₁ ^ 5 = d • 1)
    (hdetM0 : M₀.det = 1) (hdetM1 : M₁.det = 1)
    (hdetN0 : N₀.det = 1) (hdetN1 : N₁.det = 1) :
    ∃ T : GL (Fin 5) L,
      N₀ * (T : Matrix (Fin 5) (Fin 5) L) = (T : Matrix (Fin 5) (Fin 5) L) * M₀ ∧
      N₁ * (T : Matrix (Fin 5) (Fin 5) L) = (T : Matrix (Fin 5) (Fin 5) L) * M₁ := by
  classical
  obtain ⟨S, hM0S, hM1S⟩ :=
    heis_normal_form_clock_shift hκ hM0 hM1 hcM h5M hdetM0 hdetM1
  obtain ⟨T₀, hN0T, hN1T⟩ :=
    heis_normal_form_clock_shift hκ hN0 hN1 hcN h5N hdetN0 hdetN1
  set Sm : Matrix (Fin 5) (Fin 5) L := (S : Matrix (Fin 5) (Fin 5) L) with hSm
  set Si : Matrix (Fin 5) (Fin 5) L := ((S⁻¹ : GL (Fin 5) L) :
    Matrix (Fin 5) (Fin 5) L) with hSi
  set Tm : Matrix (Fin 5) (Fin 5) L := (T₀ : Matrix (Fin 5) (Fin 5) L) with hTm
  have hSiS : Si * Sm = 1 := S.inv_mul
  have hSSi : Sm * Si = 1 := S.mul_inv
  have hM0S' : M₀ * Sm = Sm * diagonal (fun i : Fin 5 => κ ^ (i : ℕ)) := by
    simpa [hSm] using hM0S
  have hM1S' : M₁ * Sm = Sm * shiftMat 1 := by simpa [hSm] using hM1S
  have hN0T' : N₀ * Tm = Tm * diagonal (fun i : Fin 5 => κ ^ (i : ℕ)) := by
    simpa [hTm] using hN0T
  have hN1T' : N₁ * Tm = Tm * shiftMat 1 := by simpa [hTm] using hN1T
  have hSiM0 : Si * M₀ = diagonal (fun i : Fin 5 => κ ^ (i : ℕ)) * Si := by
    calc Si * M₀ = Si * M₀ * (Sm * Si) := by rw [hSSi, Matrix.mul_one]
      _ = Si * (M₀ * Sm) * Si := by simp only [Matrix.mul_assoc]
      _ = Si * (Sm * diagonal (fun i : Fin 5 => κ ^ (i : ℕ))) * Si := by rw [hM0S']
      _ = diagonal (fun i : Fin 5 => κ ^ (i : ℕ)) * Si := by
        simp only [← Matrix.mul_assoc, hSiS, Matrix.one_mul]
  have hSiM1 : Si * M₁ = shiftMat 1 * Si := by
    calc Si * M₁ = Si * M₁ * (Sm * Si) := by rw [hSSi, Matrix.mul_one]
      _ = Si * (M₁ * Sm) * Si := by simp only [Matrix.mul_assoc]
      _ = Si * (Sm * shiftMat 1) * Si := by rw [hM1S']
      _ = shiftMat 1 * Si := by simp only [← Matrix.mul_assoc, hSiS, Matrix.one_mul]
  let T : GL (Fin 5) L := T₀ * S⁻¹
  have hTcoe : (T : Matrix (Fin 5) (Fin 5) L) = Tm * Si := by
    simp [T, hTm, hSi]
  have hN0 : N₀ * (T : Matrix (Fin 5) (Fin 5) L) = (T : Matrix (Fin 5) (Fin 5) L) * M₀ := by
    calc N₀ * (T : Matrix (Fin 5) (Fin 5) L) = N₀ * (Tm * Si) := by rw [hTcoe]
      _ = (N₀ * Tm) * Si := by rw [Matrix.mul_assoc]
      _ = (Tm * diagonal (fun i : Fin 5 => κ ^ (i : ℕ))) * Si := by rw [hN0T']
      _ = Tm * (diagonal (fun i : Fin 5 => κ ^ (i : ℕ)) * Si) := by rw [Matrix.mul_assoc]
      _ = Tm * (Si * M₀) := by rw [← hSiM0]
      _ = (Tm * Si) * M₀ := by rw [Matrix.mul_assoc]
      _ = (T : Matrix (Fin 5) (Fin 5) L) * M₀ := by rw [← hTcoe]
  have hN1 : N₁ * (T : Matrix (Fin 5) (Fin 5) L) = (T : Matrix (Fin 5) (Fin 5) L) * M₁ := by
    calc N₁ * (T : Matrix (Fin 5) (Fin 5) L) = N₁ * (Tm * Si) := by rw [hTcoe]
      _ = (N₁ * Tm) * Si := by rw [Matrix.mul_assoc]
      _ = (Tm * shiftMat 1) * Si := by rw [hN1T']
      _ = Tm * (shiftMat 1 * Si) := by rw [Matrix.mul_assoc]
      _ = Tm * (Si * M₁) := by rw [← hSiM1]
      _ = (Tm * Si) * M₁ := by rw [Matrix.mul_assoc]
      _ = (T : Matrix (Fin 5) (Fin 5) L) * M₁ := by rw [← hTcoe]
  exact ⟨T, hN0, hN1⟩

theorem exists_sl_conj_heis_pairs {κ : L} (hκ : IsPrimitiveRoot κ 5)
    {M₀ M₁ N₀ N₁ : Matrix (Fin 5) (Fin 5) L}
    (hM0 : IsUnit M₀) (hM1 : IsUnit M₁) (hN0 : IsUnit N₀) (hN1 : IsUnit N₁)
    (hcM : M₀ * M₁ = κ • (M₁ * M₀)) (hcN : N₀ * N₁ = κ • (N₁ * N₀))
    {c d : L} (h5M : M₁ ^ 5 = c • 1) (h5N : N₁ ^ 5 = d • 1)
    (hdetM0 : M₀.det = 1) (hdetM1 : M₁.det = 1)
    (hdetN0 : N₀.det = 1) (hdetN1 : N₁.det = 1) :
    ∃ Y : SL(5, L),
      N₀ * (Y : Matrix (Fin 5) (Fin 5) L) = (Y : Matrix (Fin 5) (Fin 5) L) * M₀ ∧
      N₁ * (Y : Matrix (Fin 5) (Fin 5) L) = (Y : Matrix (Fin 5) (Fin 5) L) * M₁ := by
  classical
  obtain ⟨T, hN0, hN1⟩ :=
    exists_conj_heis_pairs hκ hM0 hM1 hN0 hN1 hcM hcN h5M h5N hdetM0 hdetM1 hdetN0 hdetN1
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq
    (T : Matrix (Fin 5) (Fin 5) L).det (by norm_num : 0 < 5)
  have hdetT : (T : Matrix (Fin 5) (Fin 5) L).det ≠ 0 := by
    have := T.isUnit.map Matrix.detMonoidHom
    exact this.ne_zero
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact hdetT (by rw [← hμ]; norm_num)
  let Y : SL(5, L) := ⟨μ⁻¹ • (T : Matrix (Fin 5) (Fin 5) L), by
    rw [Matrix.det_smul, Fintype.card_fin, ← hμ, ← mul_pow, inv_mul_cancel₀ hμ0, one_pow]⟩
  refine ⟨Y, ?_, ?_⟩
  · change N₀ * (μ⁻¹ • (T : Matrix (Fin 5) (Fin 5) L)) =
      (μ⁻¹ • (T : Matrix (Fin 5) (Fin 5) L)) * M₀
    rw [Matrix.mul_smul, Matrix.smul_mul, hN0]
  · change N₁ * (μ⁻¹ • (T : Matrix (Fin 5) (Fin 5) L)) =
      (μ⁻¹ • (T : Matrix (Fin 5) (Fin 5) L)) * M₁
    rw [Matrix.mul_smul, Matrix.smul_mul, hN1]

end AlgClosed

end HeisNF

end Two

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five
