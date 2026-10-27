module

public import CFSG.ClassicalInvolution.Asc77.AscT8S26UModLA
public import CFSG.ClassicalInvolution.Asc77.AscT8S26UDesc
public import CFSG.ClassicalInvolution.Asc77.AscT8S26UDefs
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients

public section

namespace CFSG.ClassicalInvolution.Asc77

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem s26_proj_eq_exists {a b : SL(3, F)} (h : proj 3 F a = proj 3 F b) :
    ∃ c : Fˣ, c ^ 3 = 1 ∧
      (b : Matrix (Fin 3) (Fin 3) F) = (c : F) • (a : Matrix (Fin 3) (Fin 3) F) := by
  have h1 : a⁻¹ * b ∈ scalars 3 F := QuotientGroup.eq.mp h
  obtain ⟨c, hc, hcm⟩ := mem_scalars.mp h1
  refine ⟨c, hc, ?_⟩
  have hb : a * (a⁻¹ * b) = b := by group
  have : (b : Matrix (Fin 3) (Fin 3) F) = (a : Matrix (Fin 3) (Fin 3) F) *
      ((a⁻¹ * b : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hb]
  rw [this, hcm, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
    Matrix.mul_one]

theorem s26_comm_of_conj_fix (A : GL (Fin 3) F) (g : SL(3, F))
    (h : conjAut 3 F A (proj 3 F g) = proj 3 F g) :
    ∃ c : Fˣ, c ^ 3 = 1 ∧ (g : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) =
      (c : F) • ((A : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F)) := by
  rw [conjAut_proj] at h
  obtain ⟨c, hc, hcm⟩ := s26_proj_eq_exists h
  refine ⟨c, hc, ?_⟩
  rw [coe_slConjugation] at hcm
  have hNM : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) =
      1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc (g : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F)
      = ((c : F) • ((A : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) *
          ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))) * (A : Matrix (Fin 3) (Fin 3) F) := by
        rw [← hcm]
    _ = (c : F) • ((A : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F)) := by
        rw [Matrix.smul_mul, Matrix.mul_assoc, hNM, Matrix.mul_one]

@[expose] def s26e01 (t : F) : SL(3, F) :=
  ⟨!![1, t, 0; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem s26_coe_e01 (t : F) :
    (s26e01 t : Matrix (Fin 3) (Fin 3) F) = 1 + t • !![0, 1, 0; 0, 0, 0; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s26e01]

@[expose] def s26e02 : SL(3, F) :=
  ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem s26_fieldAut_ne_conjAut (τ : F ≃+* F) (B : GL (Fin 3) F)
    (h : fieldAut 3 F τ = conjAut 3 F B) : τ = 1 := by
  set M : Matrix (Fin 3) (Fin 3) F := (B : Matrix (Fin 3) (Fin 3) F) with hM
  set N : Matrix (Fin 3) (Fin 3) F := ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hN
  have hMN : M * N = 1 := by rw [hM, hN, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hNM : N * M = 1 := by rw [hM, hN, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  set E : Matrix (Fin 3) (Fin 3) F := !![0, 1, 0; 0, 0, 0; 0, 0, 0] with hE
  have hEE : E * E = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hE, Matrix.mul_apply, Fin.sum_univ_three]
  have key : ∀ t : F, ∃ c : Fˣ, c ^ 3 = 1 ∧ M * (1 + t • E) * N = (c : F) • (1 + τ t • E) := by
    intro t
    have h1 : fieldAut 3 F τ (proj 3 F (s26e01 t)) = conjAut 3 F B (proj 3 F (s26e01 t)) := by
      rw [h]
    rw [fieldAut_proj, conjAut_proj] at h1
    obtain ⟨c, hc, hcm⟩ := s26_proj_eq_exists h1
    refine ⟨c, hc, ?_⟩
    have e1 : ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F B
        (s26e01 t) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = M * (1 + t • E) * N := by
      rw [coe_slConjugation, s26_coe_e01]
    rw [e1] at hcm
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at hcm
    have e2 : (s26e01 t : Matrix (Fin 3) (Fin 3) F).map (τ.toRingHom) = 1 + τ t • E := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [s26e01, hE, Matrix.map_apply]
    rw [e2] at hcm
    exact hcm
  obtain ⟨c, hc, hc1⟩ := key 1
  rw [map_one] at hc1
  have hn : M * E * N = (c : F) • (1 + E) - 1 := by
    have : M * (1 + E) * N = 1 + M * E * N := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hMN]
    simp only [one_smul] at hc1
    rw [this] at hc1
    rw [← hc1]
    abel
  have hsq : (M * E * N) * (M * E * N) = 0 := by
    calc (M * E * N) * (M * E * N) = M * E * (N * M) * E * N := by simp only [Matrix.mul_assoc]
      _ = M * (E * E) * N := by
        rw [hNM, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hEE]; simp
  rw [hn] at hsq
  have h00 := congrFun (congrFun hsq 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three, hE] at h00
  have hcc : (c : F) = 1 := by linear_combination h00
  have hn' : M * E * N = E := by
    rw [hn, hcc, one_smul]
    abel
  ext t
  obtain ⟨ct, hct, hkt⟩ := key t
  have hlhs : M * (1 + t • E) * N = 1 + t • E := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hMN, Matrix.mul_smul, Matrix.smul_mul,
      hn']
  rw [hlhs] at hkt
  have e00 := congrFun (congrFun hkt 0) 0
  have e01 := congrFun (congrFun hkt 0) 1
  simp [hE] at e00 e01
  have hct1 : (ct : F) = 1 := by linear_combination -e00
  rw [hct1] at e01
  simpa using e01.symm

theorem s26_sq_mem_E [Finite F] (α : MulAut (projectiveSL 3 F)) :
    α ^ 2 ∈ semilinearAutGroup 3 F := by
  have hR : standardAutGroup 3 F = ⊤ := (automorphism_generation (K := F) (n := 3) le_rfl).1
  have hα : α ∈ standardAutGroup 3 F := by
    rw [hR]
    exact Subgroup.mem_top α
  have hδδ : dualAut 3 F * dualAut 3 F = 1 :=
    (standard_automorphism_transport (K := F) (n := 3)).2.2.2.1
  rcases mem_or_mul_dualAut_mem hα with h | h
  · exact pow_mem h 2
  · have e : α ^ 2 = (α * dualAut 3 F) * (dualAut 3 F * (α * dualAut 3 F) * dualAut 3 F) := by
      calc α ^ 2 = α * α := pow_two α
        _ = α * (dualAut 3 F * dualAut 3 F) * α * (dualAut 3 F * dualAut 3 F) := by
            rw [hδδ]
            simp
        _ = _ := by group
    rw [e]
    exact mul_mem h (dualAut_mul_mul_dualAut_mem h)

theorem s26_ringAut_eq_one [Finite F] (hodd : Odd (Nat.card (F ≃+* F))) {σ : F ≃+* F}
    (h : σ * σ = 1) : σ = 1 := by
  have h1 : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  have h2 : orderOf σ ∣ Nat.card (F ≃+* F) := orderOf_dvd_natCard σ
  have h3 : orderOf σ = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact h
    · exfalso
      rw [h] at h2
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  exact orderOf_eq_one_iff.mp h3


@[expose] def s26xS : SL(3, F) := blockSL F 3 2 0 (by norm_num) (-1)

theorem s26_coe_xS : ((s26xS : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = s26xM := by
  unfold s26xS
  rw [coe_blockSL_three_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s26xM]

theorem s26_xM_sq : (s26xM : Matrix (Fin 3) (Fin 3) F) * s26xM = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s26xM, Matrix.mul_apply, Fin.sum_univ_three]

theorem s26_xS_inv : (s26xS : SL(3, F))⁻¹ = s26xS :=
  inv_eq_of_mul_eq_one_right (Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, s26_coe_xS, s26_xM_sq,
      Matrix.SpecialLinearGroup.coe_one]))

theorem s26_slConj_scalar (A : GL (Fin 3) F) (m : F)
    (hA : (A : Matrix (Fin 3) (Fin 3) F) = m • (1 : Matrix (Fin 3) (Fin 3) F)) (g : SL(3, F)) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A g = g := by
  apply Subtype.ext
  rw [coe_slConjugation]
  have hMN : (A : Matrix (Fin 3) (Fin 3) F) * ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hc : (A : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) =
      (g : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) := by
    rw [hA, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
  rw [hc, Matrix.mul_assoc, hMN, Matrix.mul_one]

theorem s26_slConj_xN (A : GL (Fin 3) F) {m : F} (hm : m ≠ 0)
    (hA : (A : Matrix (Fin 3) (Fin 3) F) = m • s26xM) (g : SL(3, F)) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A g =
      s26xS * g * s26xS⁻¹ := by
  apply Subtype.ext
  rw [s26_xS_inv, coe_slConjugation, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, s26_coe_xS]
  set N : Matrix (Fin 3) (Fin 3) F := ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hN
  have hMN : (m • (s26xM : Matrix (Fin 3) (Fin 3) F)) * N = 1 := by
    rw [← hA, hN, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : (s26xM : Matrix (Fin 3) (Fin 3) F) * N = m⁻¹ • (1 : Matrix (Fin 3) (Fin 3) F) := by
    calc (s26xM : Matrix (Fin 3) (Fin 3) F) * N
        = m⁻¹ • (m • ((s26xM : Matrix (Fin 3) (Fin 3) F) * N)) := by
          rw [smul_smul, inv_mul_cancel₀ hm, one_smul]
      _ = m⁻¹ • (1 : Matrix (Fin 3) (Fin 3) F) := by rw [← Matrix.smul_mul, hMN]
  have h2 : N = m⁻¹ • (s26xM : Matrix (Fin 3) (Fin 3) F) := by
    calc N = (s26xM * s26xM : Matrix (Fin 3) (Fin 3) F) * N := by rw [s26_xM_sq, Matrix.one_mul]
      _ = (s26xM : Matrix (Fin 3) (Fin 3) F) * ((s26xM : Matrix (Fin 3) (Fin 3) F) * N) := by
          rw [Matrix.mul_assoc]
      _ = m⁻¹ • (s26xM : Matrix (Fin 3) (Fin 3) F) := by
          rw [h1, Matrix.mul_smul, Matrix.mul_one]
  rw [hA, h2]
  simp [smul_smul, hm]

theorem s26_psl3_main [Finite F] (h2 : (2 : F) ≠ 0) (hq3 : Nat.card F % 4 = 3)
    (hodd : Odd (Nat.card (F ≃+* F))) (φ : MulAut (projectiveSL 3 F)) {n : ℕ} (hn : 1 ≤ n)
    (hφ : φ ^ 2 ^ (n + 1) = 1) {A₀ : SL(2, F)} (hA1 : A₀ ^ 2 ^ (n + 1) = 1)
    (hA0 : A₀ ^ 2 ^ n ≠ 1)
    (hfix : φ (proj 3 F (blockSL F 3 2 0 (by norm_num) A₀)) =
      proj 3 F (blockSL F 3 2 0 (by norm_num) A₀)) :
    φ ^ 2 ^ n = 1 ∨ φ ^ 2 ^ n = MulAut.conj (proj 3 F s26xS) := by
  have hF2 : Odd (Nat.card F) := Nat.odd_iff.mpr (by omega)
  set r₀ : SL(3, F) := blockSL F 3 2 0 (by norm_num) A₀ with hr₀
  have hneg : A₀ ^ 2 ^ n = -1 := s26_sl2_pow_eq_neg_one hF2 hA1 hA0
  have hrx : r₀ ^ 2 ^ n = s26xS := by rw [hr₀, ← map_pow, hneg]; rfl
  have hr₀m : (r₀ : Matrix (Fin 3) (Fin 3) F) =
      s26R0 (A₀ 0 0) (A₀ 0 1) (A₀ 1 0) (A₀ 1 1) := by
    rw [hr₀, coe_blockSL_three_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [s26R0]
  have hdet : A₀ 0 0 * A₀ 1 1 - A₀ 0 1 * A₀ 1 0 = 1 := by
    have := A₀.2
    rw [Matrix.det_fin_two] at this
    exact this
  have hirr := s26_no_root h2 hq3 hn (A := A₀) (by rw [hneg]; simp)
  have huE : φ ^ 2 ^ n ∈ semilinearAutGroup 3 F := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ', pow_mul]
    exact pow_mem (s26_sq_mem_E φ) _
  have huu : φ ^ 2 ^ n * φ ^ 2 ^ n = 1 := by
    rw [← pow_two, ← pow_mul, ← pow_succ]
    exact hφ
  obtain ⟨A, σ, hAσ⟩ := mem_semilinearAutGroup_iff.mp huE
  have hσ : σ = 1 := by
    have h := conjAut_mul_fieldAut_mul A A σ σ
    rw [← hAσ, huu] at h
    have h' : fieldAut 3 F (σ * σ) =
        conjAut 3 F (A * GeneralLinearGroup.map (σ : F →+* F) A)⁻¹ := by
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_right h.symm
    exact s26_ringAut_eq_one hodd (s26_fieldAut_ne_conjAut _ _ h')
  rw [hσ, map_one, mul_one] at hAσ
  have hfixk : ∀ k : ℕ, (φ ^ k) (proj 3 F r₀) = proj 3 F r₀ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, MulAut.mul_apply, hfix, ih]
  have hAr : conjAut 3 F A (proj 3 F r₀) = proj 3 F r₀ := by
    rw [← hAσ]
    exact hfixk _
  have hAx : conjAut 3 F A (proj 3 F s26xS) = proj 3 F s26xS := by
    rw [← hrx, map_pow, map_pow, hAr]
  set M : Matrix (Fin 3) (Fin 3) F := (A : Matrix (Fin 3) (Fin 3) F) with hM
  set N : Matrix (Fin 3) (Fin 3) F := ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hN
  have hMN : M * N = 1 := by rw [hM, hN, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hNM : N * M = 1 := by rw [hM, hN, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hx : s26xM * M = M * s26xM := by
    obtain ⟨c, hc, hcm⟩ := s26_comm_of_conj_fix A s26xS hAx
    rw [s26_coe_xS] at hcm
    have e : s26xM = (c : F) • (M * s26xM * N) := by
      calc s26xM = s26xM * (M * N) := by rw [hMN, Matrix.mul_one]
        _ = (s26xM * M) * N := by rw [Matrix.mul_assoc]
        _ = ((c : F) • (M * s26xM)) * N := by rw [hcm]
        _ = (c : F) • (M * s26xM * N) := by rw [Matrix.smul_mul]
    have htr : Matrix.trace (s26xM : Matrix (Fin 3) (Fin 3) F) =
        (c : F) * Matrix.trace (s26xM : Matrix (Fin 3) (Fin 3) F) := by
      calc Matrix.trace (s26xM : Matrix (Fin 3) (Fin 3) F)
          = Matrix.trace ((c : F) • (M * s26xM * N)) := by rw [← e]
        _ = (c : F) * Matrix.trace (M * s26xM * N) := by rw [Matrix.trace_smul, smul_eq_mul]
        _ = (c : F) * Matrix.trace (s26xM : Matrix (Fin 3) (Fin 3) F) := by
          rw [Matrix.trace_mul_comm (M * s26xM) N, ← Matrix.mul_assoc, hNM, Matrix.one_mul]
    have htr' : Matrix.trace (s26xM : Matrix (Fin 3) (Fin 3) F) = -1 := by
      simp [Matrix.trace, Fin.sum_univ_three, s26xM]
    rw [htr'] at htr
    have hc1 : (c : F) = 1 := by linear_combination htr
    rw [hcm, hc1, one_smul]
  obtain ⟨m02, m12, m20, m21⟩ := s26_block_diag h2 hx
  have hm22 : M 2 2 ≠ 0 := by
    intro h0
    have := congrFun (congrFun hMN 2) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, m20, m21, h0] at this
  have hr : s26R0 (A₀ 0 0) (A₀ 0 1) (A₀ 1 0) (A₀ 1 1) * M =
      M * s26R0 (A₀ 0 0) (A₀ 0 1) (A₀ 1 0) (A₀ 1 1) := by
    obtain ⟨c, hc, hcm⟩ := s26_comm_of_conj_fix A r₀ hAr
    rw [hr₀m] at hcm
    have e22 := congrFun (congrFun hcm 2) 2
    simp [s26R0, Matrix.mul_apply, Fin.sum_univ_three, Matrix.smul_apply] at e22
    have hc1 : (c : F) = 1 := by
      have : (1 - (c : F)) * M 2 2 = 0 := by linear_combination e22
      have := (mul_eq_zero.mp this).resolve_right hm22
      linear_combination -this
    rw [hcm, hc1, one_smul]
  have hAA : conjAut 3 F (A * A) (proj 3 F s26e02) = proj 3 F s26e02 := by
    rw [map_mul, ← hAσ, huu]
    rfl
  obtain ⟨c₂, hc₂, hQ⟩ := s26_comm_of_conj_fix (A * A) s26e02 hAA
  rw [Units.val_mul] at hQ
  simp only [← hM] at hQ
  have hQ22 := congrFun (congrFun hQ 2) 2
  have hQ02 := congrFun (congrFun hQ 0) 2
  have hQ12 := congrFun (congrFun hQ 1) 2
  simp [s26e02, Matrix.mul_apply, Fin.sum_univ_three, Matrix.smul_apply, m02, m12, m20,
    m21] at hQ22 hQ02 hQ12
  have hc21 : (c₂ : F) = 1 := by
    have : (1 - (c₂ : F)) * (M 2 2 * M 2 2) = 0 := by linear_combination hQ22
    have h' := (mul_eq_zero.mp this).resolve_right (mul_ne_zero hm22 hm22)
    linear_combination -h'
  rw [hc21] at hQ02
  have hQ00 : (M * M) 0 0 = (M * M) 2 2 := by
    simp [Matrix.mul_apply, Fin.sum_univ_three, m02, m12, m20, m21]
    linear_combination -hQ02
  have hQ10 : (M * M) 1 0 = 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_three, m12, m20]
    linear_combination hQ12
  rcases s26_matrix_main h2 hdet hirr hx hr hm22 hQ00 hQ10 with hM1 | hM1
  · left
    rw [hAσ]
    ext x
    obtain ⟨g, rfl⟩ := proj_surjective 3 F x
    rw [conjAut_proj]
    show _ = proj 3 F g
    congr 1
    exact s26_slConj_scalar A (M 2 2) (hM.symm.trans hM1) g
  · right
    rw [hAσ]
    ext x
    obtain ⟨g, rfl⟩ := proj_surjective 3 F x
    rw [conjAut_proj, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact s26_slConj_xN A hm22 (hM.symm.trans hM1) g

theorem s26_core [Finite F] (h2 : (2 : F) ≠ 0) (hq3 : Nat.card F % 4 = 3)
    (hodd : Odd (Nat.card (F ≃+* F))) [Group.IsPerfect SL(3, F)] {Y : Type} [Group Y]
    (ψ : SL(3, F) →* Y) (hker : ψ.ker ≤ Subgroup.center SL(3, F))
    (hsurj : Function.Surjective ψ) {n : ℕ} (hn : 1 ≤ n) {A₀ : SL(2, F)}
    (hA1 : A₀ ^ 2 ^ (n + 1) = 1) (hA0 : A₀ ^ 2 ^ n ≠ 1) (β : MulAut Y)
    (hβr : β (ψ (blockSL F 3 2 0 (by norm_num) A₀)) = ψ (blockSL F 3 2 0 (by norm_num) A₀))
    (hβ : β ^ 2 ^ (n + 1) = 1) :
    β ^ 2 ^ n = 1 ∨ β ^ 2 ^ n = MulAut.conj (ψ s26xS) := by
  have hπk : (proj 3 F).ker = Subgroup.center SL(3, F) :=
    (ker_proj (n := 3) (K := F)).trans (scalars_eq_center 3 F)
  have hk : ψ.ker ≤ (proj 3 F).ker := by
    rw [hπk]
    exact hker
  obtain ⟨φ, hφ⟩ := s26_exists_isDescent hsurj hker (proj_surjective 3 F) hπk β
  have h1 : φ (proj 3 F (blockSL F 3 2 0 (by norm_num) A₀)) =
      proj 3 F (blockSL F 3 2 0 (by norm_num) A₀) := hφ _ _ hβr
  have hpow : ∀ k : ℕ, S26IsDescent ψ (proj 3 F) (β ^ k) (φ ^ k) := fun k =>
    hφ.pow hsurj hk k
  have hφ2 : φ ^ 2 ^ (n + 1) = 1 := by
    have := hpow (2 ^ (n + 1))
    rw [hβ] at this
    ext x
    obtain ⟨s, rfl⟩ := proj_surjective 3 F x
    exact this s s (by simp)
  rcases s26_psl3_main h2 hq3 hodd φ hn hφ2 hA1 hA0 h1 with h | h
  · left
    have := hpow (2 ^ n)
    rw [h] at this
    exact s26_eq_one_of_isDescent_one hsurj hπk this
  · right
    have hd := hpow (2 ^ n)
    rw [h] at hd
    have hd2 := (S26IsDescent.conj hk s26xS).inv.mul hsurj hd
    rw [inv_mul_cancel] at hd2
    have := s26_eq_one_of_isDescent_one hsurj hπk hd2
    exact (inv_mul_eq_one.mp this).symm

theorem s26_blockSL_central {B : SL(2, F)}
    (h : blockSL F 3 2 0 (by norm_num) B ∈ Subgroup.center SL(3, F)) : B = 1 := by
  rw [← scalars_eq_center] at h
  obtain ⟨c, hc, hcm⟩ := mem_scalars.mp h
  rw [coe_blockSL_three_zero] at hcm
  have e22 := congrFun (congrFun hcm 2) 2
  simp at e22
  have h1 : blockSL F 3 2 0 (by norm_num) B = 1 := by
    apply Subtype.ext
    rw [coe_blockSL_three_zero, hcm, Matrix.SpecialLinearGroup.coe_one, ← e22]
    simp
  exact blockSL_injective (by norm_num : 0 + 2 ≤ 3) (h1.trans (map_one _).symm)

theorem s26_center_of_conj {G : Type} [Group G] (g x : G)
    (h : g * x * g⁻¹ ∈ Subgroup.center G) : x ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff] at h ⊢
  intro y
  have := h (g * y * g⁻¹)
  have e : g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
  have e' : g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
  rw [e, e'] at this
  exact mul_left_cancel (mul_right_cancel this)

theorem s26_odd_of_pow_mod_four {p e : ℕ} (h : p ^ e % 4 = 3) : Odd e := by
  by_contra hne
  rw [Nat.not_odd_iff_even] at hne
  obtain ⟨k, rfl⟩ := hne
  have hsq : p ^ (k + k) = (p ^ k) ^ 2 := by
    rw [← pow_mul]
    ring_nf
  rw [hsq] at h
  rcases Nat.even_or_odd (p ^ k) with ⟨j, hj⟩ | ⟨j, hj⟩
  · rw [hj] at h
    ring_nf at h
    omega
  · rw [hj] at h
    ring_nf at h
    omega

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank in
theorem s26_aut164L (p : ℕ) [Fact p.Prime] : S26Aut164L p := by
  intro e hadm h4 Y _ ψ hker hsurj R hR s hs n hn hord β hβ hβ2
  obtain ⟨ψ, rfl⟩ : ∃ ψ₀ : SL(3, GaloisField p e) →* Y, ψ₀ = ψ := ⟨ψ, rfl⟩
  have he : e ≠ 0 := by
    have := hadm.2.1
    omega
  have hF : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e he
  have hq3 : Nat.card (GaloisField p e) % 4 = 3 := by rw [hF]; exact h4
  have hodd2 : Odd (Nat.card (GaloisField p e)) := Nat.odd_iff.mpr (by omega)
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard hodd2
  have hodd : Odd (Nat.card (GaloisField p e ≃+* GaloisField p e)) := by
    obtain ⟨σ, -, -, -, hcard, -⟩ := finite_field_automorphism_fixed_field_cardinality
      (F := GaloisField p e) (Fact.out : p.Prime) (Nat.one_le_iff_ne_zero.mpr he) hF
    rw [hcard]
    exact s26_odd_of_pow_mod_four h4
  have hperf : Group.IsPerfect SL(3, GaloisField p e) :=
    Group.isPerfect_def.2 (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero .PSL 3 p e
      Fact.out trivial hadm).1.1
  have hRl := CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 2)
    (by norm_num) hR
  obtain ⟨g, hg⟩ := (CFSG.ClassicalInvolution.Models.mem_longRootSet_iff
    (show 2 ≤ 3 by norm_num)).mp hRl
  rw [hg] at hs
  obtain ⟨r₀, hr₀, hsr⟩ := hs
  obtain ⟨A₀, rfl⟩ := hr₀
  let ψ₁ : SL(3, GaloisField p e) →* Y := ψ.comp (MulAut.conj g).toMonoidHom
  have hψ₁ : ∀ x, ψ₁ x = ψ (g * x * g⁻¹) := fun x => rfl
  have hsurj₁ : Function.Surjective ψ₁ := by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    let x' : SL(3, GaloisField p e) := x
    have hx' : g * (g⁻¹ * x' * g) * g⁻¹ = x' := by group
    refine ⟨g⁻¹ * x' * g, ?_⟩
    rw [hψ₁, hx']
    exact hx
  have hker₁ : ψ₁.ker ≤ Subgroup.center SL(3, GaloisField p e) := by
    intro x hx
    rw [MonoidHom.mem_ker, hψ₁] at hx
    exact s26_center_of_conj g x (hker hx)
  have hsr' : g * blockSL (GaloisField p e) 3 2 0 (by norm_num) A₀ * g⁻¹ = s := hsr
  have hψs : ψ₁ (blockSL (GaloisField p e) 3 2 0 (by norm_num) A₀) = ψ s := by
    rw [hψ₁, hsr']
  have hord₁ : orderOf (ψ₁ (blockSL (GaloisField p e) 3 2 0 (by norm_num) A₀)) = 2 ^ (n + 1) := by
    rw [hψs]
    exact hord
  have hA1 : A₀ ^ 2 ^ (n + 1) = 1 := by
    have h1 : (ψ₁ (blockSL (GaloisField p e) 3 2 0 (by norm_num) A₀)) ^ 2 ^ (n + 1) = 1 := by
      rw [← hord₁]
      exact pow_orderOf_eq_one _
    rw [← map_pow, ← map_pow, ← MonoidHom.mem_ker] at h1
    exact s26_blockSL_central (hker₁ h1)
  have hA0 : A₀ ^ 2 ^ n ≠ 1 := by
    intro h0
    have h1 : (ψ₁ (blockSL (GaloisField p e) 3 2 0 (by norm_num) A₀)) ^ 2 ^ n = 1 := by
      rw [← map_pow, ← map_pow, h0, map_one, map_one]
    have h3 : 2 ^ n < orderOf (ψ₁ (blockSL (GaloisField p e) 3 2 0 (by norm_num) A₀)) := by
      rw [hord₁]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    exact pow_ne_one_of_lt_orderOf (pow_ne_zero n (by norm_num)) h3 h1
  have hβ₁ : β (ψ₁ (blockSL (GaloisField p e) 3 2 0 (by norm_num) A₀)) =
      ψ₁ (blockSL (GaloisField p e) 3 2 0 (by norm_num) A₀) := by
    rw [hψs]
    exact hβ
  have hcore := s26_core (F := GaloisField p e) h2 hq3 hodd ψ₁ hker₁ hsurj₁ hn hA1 hA0 β hβ₁ hβ2
  have hx : ψ₁ s26xS = ψ s ^ 2 ^ n := by
    have hneg : A₀ ^ 2 ^ n = -1 := s26_sl2_pow_eq_neg_one hodd2 hA1 hA0
    calc ψ₁ s26xS = ψ₁ (blockSL (GaloisField p e) 3 2 0 (by norm_num) (-1)) := rfl
      _ = ψ₁ ((blockSL (GaloisField p e) 3 2 0 (by norm_num) A₀) ^ 2 ^ n) := by
          rw [← map_pow, hneg]
      _ = (ψ₁ (blockSL (GaloisField p e) 3 2 0 (by norm_num) A₀)) ^ 2 ^ n := map_pow _ _ _
      _ = ψ s ^ 2 ^ n := by rw [hψs]
  rcases hcore with h | h
  · exact Or.inl h
  · right
    rw [h, hx]
    rfl

end CFSG.ClassicalInvolution.Asc77
