module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeHeisSL3

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix

section Cyc

variable {K : Type*} [Field K]

@[expose] def signedCycMat : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; -1, 0, 0; 0, -1, 0]

theorem det_signedCycMat : (signedCycMat : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [signedCycMat, Matrix.det_fin_three]

@[expose] def signedCycSL : SpecialLinearGroup (Fin 3) K := ⟨signedCycMat, det_signedCycMat⟩

theorem coe_signedCycSL :
    ((signedCycSL : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = signedCycMat := rfl

theorem signedCycMat_sq :
    (signedCycMat : Matrix (Fin 3) (Fin 3) K) ^ 2 = !![0, -1, 0; 0, 0, -1; 1, 0, 0] := by
  rw [pow_two, signedCycMat, Matrix.mul_fin_three]
  simp

theorem signedCycMat_sq_mul : (signedCycMat : Matrix (Fin 3) (Fin 3) K) ^ 2 * signedCycMat = 1 := by
  rw [signedCycMat_sq, signedCycMat, Matrix.mul_fin_three, Matrix.one_fin_three]
  simp

theorem signedCycMat_mul_sq : (signedCycMat : Matrix (Fin 3) (Fin 3) K) * signedCycMat ^ 2 = 1 := by
  rw [← pow_succ', pow_succ, signedCycMat_sq_mul]

theorem eq_diagonal_of_mul_diagonal_eq {δ : Fin 3 → K} (hδ : Function.Injective δ)
    {A : Matrix (Fin 3) (Fin 3) K} (h : A * diagonal δ = diagonal δ * A) :
    A = diagonal fun i => A i i := by
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp
  · rw [Matrix.diagonal_apply_ne _ hij]
    have e := congrFun (congrFun h i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at e
    have e' : A i j * (δ j - δ i) = 0 := by linear_combination e
    exact (mul_eq_zero.1 e').resolve_right (sub_ne_zero.2 fun h' => hij (hδ h'.symm))

theorem eq_diagonal_mul_signedCycMat_pow {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) {γ : GL (Fin 3) K}
    {r : K} (h : (γ : Matrix (Fin 3) (Fin 3) K) * diagonal ![1, ω ^ 2, ω] =
      r • (diagonal ![1, ω ^ 2, ω] * (γ : Matrix (Fin 3) (Fin 3) K))) :
    ∃ (d : Fin 3 → K) (k : ℕ), (γ : Matrix (Fin 3) (Fin 3) K) = diagonal d * signedCycMat ^ k := by
  set A : Matrix (Fin 3) (Fin 3) K := (γ : Matrix (Fin 3) (Fin 3) K) with hA
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω3
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h2
    apply hω1
    have e : ω = ω ^ 3 := by rw [pow_succ, h2, one_mul]
    rw [e, hω3]
  have hω21 : ω ^ 2 ≠ ω := by
    intro h2
    apply hω1
    have e : ω * (ω - 1) = 0 := by linear_combination h2
    exact sub_eq_zero.1 ((mul_eq_zero.1 e).resolve_left hω0)
  have hinj : Function.Injective ![(1 : K), ω ^ 2, ω] := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | exact absurd (show (1 : K) = ω ^ 2 from hij) (Ne.symm hω2)
      | exact absurd (show (1 : K) = ω from hij) (Ne.symm hω1)
      | exact absurd (show ω ^ 2 = (1 : K) from hij) hω2
      | exact absurd (show ω ^ 2 = ω from hij) hω21
      | exact absurd (show ω = (1 : K) from hij) hω1
      | exact absurd (show ω = ω ^ 2 from hij) (Ne.symm hω21)
  have hCΔ : signedCycMat * diagonal ![1, ω ^ 2, ω] =
      ω • (diagonal ![1, ω ^ 2, ω] * signedCycMat) := by
    rw [signedCycMat]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    all_goals first | linear_combination | linear_combination hω3 | linear_combination -hω3
  have hC2Δ : signedCycMat ^ 2 * diagonal ![1, ω ^ 2, ω] =
      ω ^ 2 • (diagonal ![1, ω ^ 2, ω] * signedCycMat ^ 2) := by
    calc signedCycMat ^ 2 * diagonal ![1, ω ^ 2, ω]
        = signedCycMat * (signedCycMat * diagonal ![1, ω ^ 2, ω]) := by
          rw [pow_two, Matrix.mul_assoc]
      _ = signedCycMat * (ω • (diagonal ![1, ω ^ 2, ω] * signedCycMat)) := by rw [hCΔ]
      _ = ω • ((signedCycMat * diagonal ![1, ω ^ 2, ω]) * signedCycMat) := by
          rw [Matrix.mul_smul, Matrix.mul_assoc]
      _ = ω • ((ω • (diagonal ![1, ω ^ 2, ω] * signedCycMat)) * signedCycMat) := by rw [hCΔ]
      _ = (ω * ω) • (diagonal ![1, ω ^ 2, ω] * (signedCycMat * signedCycMat)) := by
          rw [Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
      _ = ω ^ 2 • (diagonal ![1, ω ^ 2, ω] * signedCycMat ^ 2) := by
          rw [pow_two ω, pow_two (signedCycMat : Matrix (Fin 3) (Fin 3) K)]
  have hrow : A 0 0 ≠ 0 ∨ A 0 1 ≠ 0 ∨ A 0 2 ≠ 0 := by
    by_contra hc
    push Not at hc
    have hdet : A.det = 0 := by
      rw [Matrix.det_fin_three, hc.1, hc.2.1, hc.2.2]
      ring
    have hu := congrArg Matrix.det (Units.mul_inv γ)
    rw [Matrix.det_mul, Matrix.det_one, ← hA, hdet, zero_mul] at hu
    exact zero_ne_one hu
  have he : ∀ j, A 0 j * (![1, ω ^ 2, ω] j - r) = 0 := by
    intro j
    have e := congrFun (congrFun h 0) j
    rw [Matrix.mul_diagonal, Matrix.smul_apply, Matrix.diagonal_mul, smul_eq_mul] at e
    have e0 : (![1, ω ^ 2, ω] : Fin 3 → K) 0 = 1 := rfl
    rw [e0, one_mul] at e
    linear_combination e
  rcases hrow with h0 | h0 | h0
  · have hr : r = 1 := by
      have e := (mul_eq_zero.1 (he 0)).resolve_left h0
      have e0 : (![1, ω ^ 2, ω] : Fin 3 → K) 0 = 1 := rfl
      rw [e0] at e
      linear_combination -e
    rw [hr, one_smul] at h
    refine ⟨fun i => A i i, 0, ?_⟩
    rw [pow_zero, Matrix.mul_one]
    exact eq_diagonal_of_mul_diagonal_eq hinj h
  · have hr : r = ω ^ 2 := by
      have e := (mul_eq_zero.1 (he 1)).resolve_left h0
      have e1 : (![1, ω ^ 2, ω] : Fin 3 → K) 1 = ω ^ 2 := rfl
      rw [e1] at e
      linear_combination -e
    rw [hr] at h
    have hcomm : (A * signedCycMat) * diagonal ![1, ω ^ 2, ω] =
        diagonal ![1, ω ^ 2, ω] * (A * signedCycMat) := by
      calc (A * signedCycMat) * diagonal ![1, ω ^ 2, ω]
          = A * (signedCycMat * diagonal ![1, ω ^ 2, ω]) := Matrix.mul_assoc _ _ _
        _ = ω • ((A * diagonal ![1, ω ^ 2, ω]) * signedCycMat) := by
            rw [hCΔ, Matrix.mul_smul, Matrix.mul_assoc]
        _ = (ω * ω ^ 2) • (diagonal ![1, ω ^ 2, ω] * (A * signedCycMat)) := by
            rw [h, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
        _ = diagonal ![1, ω ^ 2, ω] * (A * signedCycMat) := by
            rw [show ω * ω ^ 2 = ω ^ 3 by ring, hω3, one_smul]
    refine ⟨fun i => (A * signedCycMat : Matrix (Fin 3) (Fin 3) K) i i, 2, ?_⟩
    rw [← eq_diagonal_of_mul_diagonal_eq hinj hcomm, Matrix.mul_assoc, signedCycMat_mul_sq,
      Matrix.mul_one]
  · have hr : r = ω := by
      have e := (mul_eq_zero.1 (he 2)).resolve_left h0
      have e2 : (![1, ω ^ 2, ω] : Fin 3 → K) 2 = ω := rfl
      rw [e2] at e
      linear_combination -e
    rw [hr] at h
    have hcomm : (A * signedCycMat ^ 2) * diagonal ![1, ω ^ 2, ω] =
        diagonal ![1, ω ^ 2, ω] * (A * signedCycMat ^ 2) := by
      calc (A * signedCycMat ^ 2) * diagonal ![1, ω ^ 2, ω]
          = A * (signedCycMat ^ 2 * diagonal ![1, ω ^ 2, ω]) := Matrix.mul_assoc _ _ _
        _ = ω ^ 2 • ((A * diagonal ![1, ω ^ 2, ω]) * signedCycMat ^ 2) := by
            rw [hC2Δ, Matrix.mul_smul, Matrix.mul_assoc]
        _ = (ω ^ 2 * ω) • (diagonal ![1, ω ^ 2, ω] * (A * signedCycMat ^ 2)) := by
            rw [h, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
        _ = diagonal ![1, ω ^ 2, ω] * (A * signedCycMat ^ 2) := by
            rw [show ω ^ 2 * ω = ω ^ 3 by ring, hω3, one_smul]
    refine ⟨fun i => (A * signedCycMat ^ 2 : Matrix (Fin 3) (Fin 3) K) i i, 1, ?_⟩
    rw [pow_one, ← eq_diagonal_of_mul_diagonal_eq hinj hcomm, Matrix.mul_assoc, signedCycMat_sq_mul,
      Matrix.mul_one]

end Cyc

section Cyclic

variable {K : Type*} [Field K]

theorem eq_zero_of_add_smul_mulVec_eq_zero {α : K} (hα : ∀ b : K, b ^ 3 ≠ α)
    {A : Matrix (Fin 3) (Fin 3) K} (hA : A ^ 3 = α • 1) {v : Fin 3 → K} (hv : v ≠ 0)
    {a b c : K} (h : a • v + b • (A *ᵥ v) + c • (A *ᵥ (A *ᵥ v)) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  by_contra hne
  set p : Polynomial K :=
    Polynomial.C a + Polynomial.C b * Polynomial.X + Polynomial.C c * Polynomial.X ^ 2 with hp
  have hp0 : p ≠ 0 := by
    intro h0
    apply hne
    have e0 := congrArg (fun q : Polynomial K => q.coeff 0) h0
    have e1 := congrArg (fun q : Polynomial K => q.coeff 1) h0
    have e2 := congrArg (fun q : Polynomial K => q.coeff 2) h0
    simp [hp, Polynomial.coeff_X, Polynomial.coeff_X_pow, Polynomial.coeff_C] at e0 e1 e2
    exact ⟨e0, e1, e2⟩
  have hmon : (Polynomial.X ^ 3 - Polynomial.C α : Polynomial K).Monic :=
    Polynomial.monic_X_pow_sub_C α (by norm_num)
  have hirr : Irreducible (Polynomial.X ^ 3 - Polynomial.C α : Polynomial K) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_three hα
  have hdeg : p.natDegree < (Polynomial.X ^ 3 - Polynomial.C α : Polynomial K).natDegree := by
    rw [Polynomial.natDegree_X_pow_sub_C]
    have : p.natDegree ≤ 2 := by
      rw [hp]
      compute_degree
    omega
  obtain ⟨s, t, hst⟩ :=
    (hirr.coprime_iff_not_dvd).2 (hmon.not_dvd_of_natDegree_lt hp0 hdeg)
  have haeval : Polynomial.aeval A (Polynomial.X ^ 3 - Polynomial.C α) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hA,
      Algebra.algebraMap_eq_smul_one, sub_self]
  have hunit : Polynomial.aeval A t * Polynomial.aeval A p = 1 := by
    have e := congrArg (Polynomial.aeval A) hst
    rwa [map_add, map_mul, map_mul, haeval, mul_zero, zero_add, map_one] at e
  have hpA : Polynomial.aeval A p = a • 1 + b • A + c • (A * A) := by
    rw [hp, map_add, map_add, map_mul, map_mul, Polynomial.aeval_C, Polynomial.aeval_C,
      Polynomial.aeval_C, map_pow, Polynomial.aeval_X, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.one_mul, Matrix.one_mul, pow_two]
  have hpv : Polynomial.aeval A p *ᵥ v = 0 := by
    rw [hpA, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    exact h
  apply hv
  calc v = (Polynomial.aeval A t * Polynomial.aeval A p) *ᵥ v := by
        rw [hunit, Matrix.one_mulVec]
    _ = Polynomial.aeval A t *ᵥ (Polynomial.aeval A p *ᵥ v) := (Matrix.mulVec_mulVec _ _ _).symm
    _ = 0 := by rw [hpv, Matrix.mulVec_zero]

end Cyclic

section NormalForm

variable {K : Type*} [Field K]

theorem exists_SL_conj_offDiag_eq_zero {γ P : GL (Fin 3) K}
    (hP : ∀ i j, i ≠ j → ((P * γ * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j = 0) :
    ∃ z : SpecialLinearGroup (Fin 3) K, ∀ i j, i ≠ j →
      ((SpecialLinearGroup.toGL z * γ * (SpecialLinearGroup.toGL z)⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) i j = 0 := by
  set u : Kˣ := GeneralLinearGroup.det P with hu
  have h1 : diagonal ![((u⁻¹ : Kˣ) : K), 1, 1] * diagonal ![(u : K), 1, 1] = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  have h2 : diagonal ![(u : K), 1, 1] * diagonal ![((u⁻¹ : Kˣ) : K), 1, 1] = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  set D : GL (Fin 3) K := ⟨_, _, h1, h2⟩ with hD
  have hdet : ((D * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [Units.val_mul, Matrix.det_mul, ← GeneralLinearGroup.val_det_apply P, ← hu]
    show (diagonal ![((u⁻¹ : Kˣ) : K), 1, 1]).det * (u : K) = 1
    rw [det_diagonal, Fin.prod_univ_three]
    simp
  refine ⟨⟨_, hdet⟩, fun i j hij => ?_⟩
  have hz : SpecialLinearGroup.toGL (⟨_, hdet⟩ : SpecialLinearGroup (Fin 3) K) = D * P :=
    Units.ext rfl
  rw [hz, show D * P * γ * (D * P)⁻¹ = D * (P * γ * P⁻¹) * D⁻¹ by group]
  show (diagonal ![((u⁻¹ : Kˣ) : K), 1, 1] *
    ((P * γ * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal ![(u : K), 1, 1]) i j = 0
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hP i j hij, mul_zero, zero_mul]

theorem eq_diagonal_mul_signedCycMat_pow_zero {M : Matrix (Fin 3) (Fin 3) K}
    (h : ∀ i j, i ≠ j → M i j = 0) : M = diagonal (fun i => M i i) * signedCycMat ^ 0 := by
  rw [pow_zero, Matrix.mul_one]
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp
  · rw [h i j hij, Matrix.diagonal_apply_ne _ hij]

theorem exists_conj_eq_diagonal_mul_signedCycMat_pow (hζ : ∃ ζ : K, IsPrimitiveRoot ζ 3)
    {γ : GL (Fin 3) K} {α : K} (hγ : (γ : Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1) :
    ∃ (z : SpecialLinearGroup (Fin 3) K) (d : Fin 3 → K) (k : ℕ),
      ((SpecialLinearGroup.toGL z * γ * (SpecialLinearGroup.toGL z)⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = diagonal d * signedCycMat ^ k := by
  have hα0 : α ≠ 0 := ne_zero_of_pow_three_eq_smul hγ
  by_cases hcube : ∃ μ : K, μ ^ 3 = α
  · obtain ⟨μ, hμ⟩ := hcube
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      exact hα0 (by rw [← hμ]; ring)
    set s : GL (Fin 3) K := GeneralLinearGroup.scalar (Fin 3) (Units.mk0 μ hμ0) with hs
    set γ' : GL (Fin 3) K := s⁻¹ * γ with hγ'
    have hsγ : Commute s⁻¹ γ :=
      (show Commute s γ from GeneralLinearGroup.scalar_commute _ γ).inv_left
    have hγ'3 : γ' ^ 3 = 1 := by
      rw [hγ', hsγ.mul_pow]
      apply Units.ext
      have e1 : ((s⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) μ⁻¹ := by
        rw [hs, ← map_inv, GeneralLinearGroup.coe_scalar, Units.val_inv_eq_inv_val,
          Units.val_mk0]
      have e2 : (α • 1 : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) α := by
        rw [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
      rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, e1, hγ, e2,
        ← map_pow, ← map_mul, Units.val_one, ← hμ, ← mul_pow, inv_mul_cancel₀ hμ0, one_pow,
        map_one]
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcommE : ∀ x ∈ Subgroup.zpowers γ', ∀ y ∈ Subgroup.zpowers γ', x * y = y * x := by
      rintro x ⟨m, rfl⟩ y ⟨n, rfl⟩
      exact (Commute.zpow_zpow_self γ' m n).eq
    have hexpE : ∀ x ∈ Subgroup.zpowers γ', x ^ 3 = 1 := by
      rintro x ⟨m, rfl⟩
      rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
        _root_.zpow_natCast, hγ'3, _root_.one_zpow]
    obtain ⟨P, hP⟩ := RankThree.PartOne.CTP.exists_conj_diagonal_of_exponent_prime (p := 3)
      hζ _ hcommE hexpE
    have hoff := hP γ' (Subgroup.mem_zpowers γ')
    have hPγ : ∀ i j, i ≠ j →
        ((P * γ * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
      intro i j hij
      have e : P * γ * P⁻¹ = s * (P * γ' * P⁻¹) := by
        have hγs : γ = s * γ' := by rw [hγ', mul_inv_cancel_left]
        have hsP : s * P = P * s := GeneralLinearGroup.scalar_commute _ P
        rw [hγs, ← mul_assoc P s, ← hsP]
        group
      rw [e, Units.val_mul, hs, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_mul, hoff i j hij, mul_zero]
    obtain ⟨z, hz⟩ := exists_SL_conj_offDiag_eq_zero hPγ
    exact ⟨z, _, 0, eq_diagonal_mul_signedCycMat_pow_zero hz⟩
  · have hα' : ∀ b : K, b ^ 3 ≠ α := fun b hb => hcube ⟨b, hb⟩
    set A : Matrix (Fin 3) (Fin 3) K := (γ : Matrix (Fin 3) (Fin 3) K) with hA
    set v : Fin 3 → K := Pi.single 0 1 with hv
    have hv0 : v ≠ 0 := by
      intro h0
      have e := congrFun h0 0
      simp [hv] at e
    set c1 : Fin 3 → K := A *ᵥ v with hc1
    set c2 : Fin 3 → K := A *ᵥ c1 with hc2
    have hA3 : A *ᵥ c2 = α • v := by
      rw [hc2, hc1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← pow_three', hγ,
        Matrix.smul_mulVec, Matrix.one_mulVec]
    set B : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i j => ![v, c1, c2] j i with hB
    have hBdet : B.det ≠ 0 := by
      intro h0
      obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
      have e : w 0 • v + w 1 • c1 + w 2 • c2 = 0 := by
        rw [← hw]
        funext i
        simp only [hB, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.tail_cons, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        ring
      obtain ⟨e0, e1, e2⟩ := eq_zero_of_add_smul_mulVec_eq_zero hα' hγ hv0 e
      apply hw0
      funext i
      fin_cases i
      exacts [e0, e1, e2]
    set lam : K := B.det⁻¹ with hlam
    have hlam0 : lam ≠ 0 := inv_ne_zero hBdet
    set B' : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i j => ![lam • v, c1, c2] j i with hB'
    have hB'det : B'.det = 1 := by
      have e : B'.det = lam * B.det := by
        rw [Matrix.det_fin_three, Matrix.det_fin_three]
        simp [hB', hB] <;> ring
      rw [e, hlam, inv_mul_cancel₀ hBdet]
    set M : Matrix (Fin 3) (Fin 3) K := diagonal ![α / lam, -lam, -1] * signedCycMat with hM
    have hAB : A * B' = B' * M := by
      ext i j
      fin_cases j
      · show (A *ᵥ (lam • v)) i = (B' * M) i 0
        rw [Matrix.mulVec_smul, ← hc1]
        simp [hB', hM, signedCycMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring
      · show (A *ᵥ c1) i = (B' * M) i 1
        rw [← hc2]
        simp [hB', hM, signedCycMat, Matrix.mul_apply, Fin.sum_univ_three]
      · show (A *ᵥ c2) i = (B' * M) i 2
        rw [hA3]
        simp [hB', hM, signedCycMat, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp
    set Z : SpecialLinearGroup (Fin 3) K := ⟨B', hB'det⟩ with hZ
    refine ⟨Z⁻¹, ![α / lam, -lam, -1], 1, ?_⟩
    have hZZ : ((Z⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * B' = 1 := by
      have e := congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K))
        (inv_mul_cancel Z)
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at e
      exact e
    have e : (SpecialLinearGroup.toGL Z⁻¹)⁻¹ = SpecialLinearGroup.toGL Z := by
      rw [map_inv, inv_inv]
    rw [e, pow_one, ← hM, Units.val_mul, Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix,
      SpecialLinearGroup.coe_GL_coe_matrix, ← hA]
    show ((Z⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A * B' = M
    rw [Matrix.mul_assoc, hAB, ← Matrix.mul_assoc, hZZ, Matrix.one_mul]

end NormalForm

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
